#!/usr/bin/env python3
"""
Simulate parallel Holmake scheduling under different pickers.

Input:
  --graph FILE  Holmake --json dep graph (see tools/Holmake/tests/json-strings/)
  --log FILE    hol4-<ts> build log (see src/postkernel/Theory.sml
                maybe_log_time_to_disk).  Format:  <key> <seconds>
  -j N          worker count (default: 8)

Output:
  Simulated wallclock makespan for three pickers on the given graph
  and cost oracle, plus two theoretical lower bounds.

Uses only stdlib (no HOL machinery).  Doesn't touch Holmake.
"""
from __future__ import annotations
import argparse, heapq, json, os, re, statistics, sys
from collections import defaultdict

# --------------------------------------------------------------------
# graph loading

def load_graph(path: str):
    """Load Holmake --json output.  Works around HM_DepGraph.sml:242
    failing to escape " inside command strings by redacting the
    command field before JSON parsing."""
    with open(path) as f:
        text = f.read()
    text = re.sub(r'"command" : ".*",\n', '"command" : "",\n', text)
    return json.loads(text)


# --------------------------------------------------------------------
# cost oracle

def load_log(path: str) -> dict[str, float]:
    log = {}
    with open(path) as f:
        for line in f:
            parts = line.rstrip('\n').split(' ')
            if len(parts) == 2:
                try:
                    log[parts[0]] = float(parts[1])
                except ValueError:
                    pass
    return log


def theory_key(target: str, holdir: str) -> str | None:
    """Recover the log key from a *Theory.dat target path.
    /repo/src/x/y/fooTheory.dat  ->  src/x/y/foo"""
    prefix = holdir.rstrip('/') + '/'
    if not target.startswith(prefix):
        return None
    rel = target[len(prefix):]
    if not rel.endswith('Theory.dat'):
        return None
    return rel[:-len('Theory.dat')]


def build_cost_table(nodes, log, holdir, default_cost):
    """Return (cost[], coverage report).  cost[i] is 0 if the node is
    already built (needs_rebuild=false); otherwise the log entry for
    theory nodes, or default_cost for everything else."""
    n = len(nodes)
    cost = [0.0] * n
    n_theory = 0
    n_matched = 0
    n_theory_rebuild = 0
    n_nonthy_rebuild = 0
    for node in nodes:
        i = node['node_id']
        if not node['needs_rebuild']:
            cost[i] = 0.0
            continue
        if node['target'].endswith('Theory.dat'):
            n_theory += 1
            n_theory_rebuild += 1
            k = theory_key(node['target'], holdir)
            if k is not None and k in log:
                cost[i] = log[k]
                n_matched += 1
            else:
                cost[i] = default_cost
        else:
            n_nonthy_rebuild += 1
            cost[i] = default_cost
    report = {
        'total_nodes': n,
        'need_rebuild': n_theory_rebuild + n_nonthy_rebuild,
        'theory_rebuild': n_theory_rebuild,
        'theory_matched': n_matched,
        'nonthy_rebuild': n_nonthy_rebuild,
        'default_cost': default_cost,
    }
    return cost, report


# --------------------------------------------------------------------
# graph structure derived once at load time

class Graph:
    """Compact representation of the sub-DAG of nodes needing rebuild.
    Predecessors that are needs_rebuild=false are elided (they add no
    wait).  Successors are inverted from `dependencies`.
    Critical-path weights are computed via reverse topological order."""

    def __init__(self, raw_nodes, cost):
        n = len(raw_nodes)
        # sanity: node_ids are 0..n-1 (Holmake's invariant)
        assert all(node['node_id'] == i for i, node in enumerate(raw_nodes)), \
            "node_ids are expected to be 0..n-1"
        self.n = n
        self.cost = cost
        self.needs = [bool(node['needs_rebuild']) for node in raw_nodes]
        self.targets = [node['target'] for node in raw_nodes]

        # Effective predecessors: only those that also need rebuild.
        # Effective successors: inverse.
        eff_preds = [[] for _ in range(n)]
        eff_succs = [[] for _ in range(n)]
        for i, node in enumerate(raw_nodes):
            if not self.needs[i]:
                continue
            for j in node['dependencies']:
                if self.needs[j]:
                    eff_preds[i].append(j)
                    eff_succs[j].append(i)
        self.preds = eff_preds
        self.succs = eff_succs

        # Critical-path weight: cp[i] = cost[i] + max cp[j] over succs.
        # Compute by reverse-topological walk (deepest sinks first).
        self.cp_weight = self._compute_cp()

    def _compute_cp(self):
        # Iterative topological sort on the rebuild sub-DAG.
        n = self.n
        indeg = [len(self.preds[i]) if self.needs[i] else -1 for i in range(n)]
        order = []
        stack = [i for i in range(n) if self.needs[i] and indeg[i] == 0]
        while stack:
            i = stack.pop()
            order.append(i)
            for j in self.succs[i]:
                indeg[j] -= 1
                if indeg[j] == 0:
                    stack.append(j)
        if len(order) != sum(1 for x in self.needs if x):
            raise RuntimeError("cycle detected in rebuild sub-DAG")
        cp = [0.0] * n
        for i in reversed(order):
            best = 0.0
            for j in self.succs[i]:
                if cp[j] > best:
                    best = cp[j]
            cp[i] = self.cost[i] + best
        return cp


# --------------------------------------------------------------------
# simulator

def simulate(g: Graph, num_workers: int, priority_fn) -> tuple[float, list]:
    """Event-driven simulation.
    priority_fn(i) -> sort key; the picker pops the ready node with
    the SMALLEST key (so negate for max-priority pickers).
    Returns (makespan, done-order)."""
    n = g.n
    remaining = [len(g.preds[i]) if g.needs[i] else -1 for i in range(n)]
    ready = []  # min-heap of (priority, node_id)
    for i in range(n):
        if g.needs[i] and remaining[i] == 0:
            heapq.heappush(ready, (priority_fn(i), i))
    running = []  # min-heap of (completion_time, node_id)
    now = 0.0
    order = []
    while running or ready:
        while len(running) < num_workers and ready:
            _, i = heapq.heappop(ready)
            heapq.heappush(running, (now + g.cost[i], i))
        t, i = heapq.heappop(running)
        now = t
        order.append(i)
        for j in g.succs[i]:
            remaining[j] -= 1
            if remaining[j] == 0:
                heapq.heappush(ready, (priority_fn(j), j))
    return now, order


# --------------------------------------------------------------------
# pickers

def picker_insertion(g: Graph):
    """Smallest node_id first (mirrors HM_DepGraph.find_runnable_pred)."""
    return lambda i: i

def picker_lpt(g: Graph):
    """Largest cost first.  Tie-break on node_id for determinism."""
    return lambda i: (-g.cost[i], i)

def picker_hlfet(g: Graph):
    """Largest critical-path weight first.  Tie-break on node_id."""
    return lambda i: (-g.cp_weight[i], i)


# --------------------------------------------------------------------
# report

def fmt(secs: float) -> str:
    m, s = divmod(secs, 60)
    if m < 60:
        return f'{secs:8.1f}s  ({int(m)}m{s:04.1f}s)'
    h, m = divmod(m, 60)
    return f'{secs:8.1f}s  ({int(h)}h{int(m):02d}m{s:04.1f}s)'


def report(g: Graph, coverage: dict, num_workers: int, results: dict,
           lower_bounds: dict, top_cp: int = 0):
    print()
    print(f'graph: {coverage["total_nodes"]} nodes total, '
          f'{coverage["need_rebuild"]} need rebuild')
    print(f'  theory nodes needing rebuild: {coverage["theory_rebuild"]}, '
          f'matched to log: {coverage["theory_matched"]} '
          f'({100 * coverage["theory_matched"] / max(1, coverage["theory_rebuild"]):.1f}%)')
    print(f'  non-theory rebuild nodes: {coverage["nonthy_rebuild"]}  '
          f'(default cost = {coverage["default_cost"]}s)')
    print()
    print(f'workers (j) = {num_workers}')
    print(f'{"":22s}{"simulated makespan":>28s}')
    for name, makespan in results.items():
        print(f'  {name:20s}{fmt(makespan):>28s}')
    print(f'  {"-"*20:20s}')
    print(f'  {"lower bound Σc/j":20s}{fmt(lower_bounds["sum_over_j"]):>28s}')
    print(f'  {"critical path":20s}{fmt(lower_bounds["cp"]):>28s}')

    if top_cp:
        print()
        print(f'Top {top_cp} nodes by critical-path weight:')
        idxs = sorted(range(g.n), key=lambda i: -g.cp_weight[i])[:top_cp]
        for i in idxs:
            if g.needs[i]:
                print(f'  cp={g.cp_weight[i]:8.1f}s  cost={g.cost[i]:7.1f}s  '
                      f'{g.targets[i]}')


# --------------------------------------------------------------------
# entry

def selftest():
    """Two hand-built cases; assert HLFET beats insertion where expected."""
    # Case 1: A trivial chain X → Y where X (small) blocks Y (huge).
    # With j=2 and a bunch of small independent nodes, insertion picks the
    # small ones first, delaying Y.  HLFET sees Y downstream of X and picks
    # X immediately.
    nodes = [
        # node 0..3: independent small tasks
        {'node_id': 0, 'target': '/x/a.uo', 'dir': '.', 'dependencies': [],
         'needs_rebuild': True},
        {'node_id': 1, 'target': '/x/b.uo', 'dir': '.', 'dependencies': [],
         'needs_rebuild': True},
        {'node_id': 2, 'target': '/x/c.uo', 'dir': '.', 'dependencies': [],
         'needs_rebuild': True},
        {'node_id': 3, 'target': '/x/d.uo', 'dir': '.', 'dependencies': [],
         'needs_rebuild': True},
        # node 4: X — small predecessor of Y
        {'node_id': 4, 'target': '/x/X.uo', 'dir': '.', 'dependencies': [],
         'needs_rebuild': True},
        # node 5: Y — huge, depends on X
        {'node_id': 5, 'target': '/x/Y.uo', 'dir': '.', 'dependencies': [4],
         'needs_rebuild': True},
    ]
    cost = [1.0, 1.0, 1.0, 1.0, 1.0, 100.0]
    g = Graph(nodes, cost)
    ins, _ = simulate(g, 2, picker_insertion(g))
    hl,  _ = simulate(g, 2, picker_hlfet(g))
    print(f'case 1  (j=2, 4 small + X→Y_huge):  insertion={ins:.1f}s  HLFET={hl:.1f}s')
    assert hl < ins, f'HLFET should beat insertion, got {hl} vs {ins}'

    # Case 2: sanity — with j = infinity, both hit the CP.
    inf = 100
    ins2, _ = simulate(g, inf, picker_insertion(g))
    hl2,  _ = simulate(g, inf, picker_hlfet(g))
    print(f'case 2  (j=inf, same graph):        insertion={ins2:.1f}s  HLFET={hl2:.1f}s')
    assert abs(ins2 - hl2) < 1e-6, 'at j=inf both pickers should tie at CP'
    assert abs(hl2 - 101.0) < 1e-6, f'CP = X(1) + Y(100) = 101, got {hl2}'
    print('selftest OK')


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--test', action='store_true', help='run built-in selftest and exit')
    ap.add_argument('--graph', help='Holmake --json output')
    ap.add_argument('--log',   help='hol4-<ts> timing log')
    ap.add_argument('--holdir', default='/repo',
                    help='HOL root prefix stripped from targets (default /repo)')
    ap.add_argument('-j', '--jobs', type=int, default=8, help='worker count')
    ap.add_argument('--default-cost', type=float, default=0.1,
                    help='cost (secs) for nodes with no log entry (default 0.1)')
    ap.add_argument('--top-cp', type=int, default=0,
                    help='list top N nodes on the critical path')
    args = ap.parse_args()
    if args.test:
        selftest()
        return
    if not args.graph or not args.log:
        ap.error('--graph and --log are required (or use --test)')

    nodes = load_graph(args.graph)
    log = load_log(args.log)
    cost, coverage = build_cost_table(nodes, log, args.holdir, args.default_cost)
    g = Graph(nodes, cost)

    results = {}
    for name, mk_pri in [
        ('insertion (current)', picker_insertion),
        ('LPT', picker_lpt),
        ('HLFET', picker_hlfet),
    ]:
        pri = mk_pri(g)
        makespan, _ = simulate(g, args.jobs, pri)
        results[name] = makespan

    sum_c = sum(g.cost[i] for i in range(g.n) if g.needs[i])
    cp = max((g.cp_weight[i] for i in range(g.n) if g.needs[i]), default=0.0)
    lower_bounds = {'sum_over_j': sum_c / args.jobs, 'cp': cp}
    report(g, coverage, args.jobs, results, lower_bounds, top_cp=args.top_cp)


if __name__ == '__main__':
    main()
