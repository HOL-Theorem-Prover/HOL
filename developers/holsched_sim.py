#!/usr/bin/env python3
"""
Simulate parallel Holmake scheduling under different pickers.

Input:
  --graph FILE  Holmake --json dep graph (see tools/Holmake/tests/json-strings/)
  --log FILE    <key> <seconds> cost data: either a hol4-<ts> build log (see
                src/postkernel/Theory.sml maybe_log_time_to_disk) or a
                .hol/build-logs/target-times cache.  Used for DURATIONS --
                how long each job really takes.
  --priority-log FILE
                the cost data the SCHEDULER gets to see (default: --log).
                Separating the two is the whole point: it answers "what does
                a schedule built from degraded information cost in real
                time?", which is exactly the cold-checkout question.
  --seed FILE   a committed seed file, merged UNDER --priority-log
                (priority-log entries win per key), mirroring how
                target_times would consume one.
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

def load_log(path: str, min_cost: float = 0.0) -> dict[str, float]:
    """Read <key> <seconds> lines.  `#' comments and malformed lines are
    skipped; entries below min_cost are dropped, which is how the seed
    threshold sweep is done."""
    log = {}
    with open(path) as f:
        for line in f:
            if line.lstrip().startswith('#'):
                continue
            parts = line.split()
            if len(parts) == 2:
                try:
                    v = float(parts[1])
                except ValueError:
                    continue
                if v >= min_cost:
                    log[parts[0]] = v
    return log


THEORY_SUFFIXES = ('Theory.dat', 'Theory.sml', 'Theory.sig')


def rel_to_root(path: str, holdir: str, root: str | None = None) -> str:
    """Mirror Holmake_tools.rel_to_root: relative to the project root,
    else `$(HOLDIR)/'-prefixed, else left absolute."""
    for base, pfx in ((root or holdir, ''), (holdir, '$(HOLDIR)/')):
        base = base.rstrip('/')
        if path.startswith(base + '/'):
            return pfx + path[len(base) + 1:]
    return path


def node_key(target: str, holdir: str, root: str | None = None) -> str:
    """Mirror HM_DepGraph.cost_key.

    A theory node is keyed by its theory name under its directory --
    /repo/src/x/y/fooTheory.dat -> src/x/y/foo -- which is what the
    BIC_BuildScript path reduces to and what Theory.sml's thy_log_key
    writes.  Every other node is keyed by its own target path, so the
    two spaces cannot collide."""
    for sfx in THEORY_SUFFIXES:
        if target.endswith(sfx):
            target = target[:-len(sfx)]
            break
    return rel_to_root(target, holdir, root)


def is_theory_node(target: str) -> bool:
    return any(target.endswith(sfx) for sfx in THEORY_SUFFIXES)


def build_tables(nodes, pri_log, dur_log, holdir, default_duration,
                 all_rebuild):
    """Return (pri[], dur[], needs[], coverage).

    `pri' is what the scheduler weighs: the log value for the node's key,
    or 0.0 when absent -- exactly what target_times.cost answers, so a
    missing entry degrades the schedule the same way it does in the real
    build.

    `dur' is how long the node really takes.  A theory's three
    Theory.{dat,sml,sig} siblings share one BIC_BuildScript job
    (Holmake.sml:1695-1697) and complete together, so the duration is
    charged to the .dat sibling alone and the group is collapsed into a
    single task in Graph; charging all three would triple-count every
    theory in the build."""
    n = len(nodes)
    pri = [0.0] * n
    dur = [0.0] * n
    needs = [True if all_rebuild else bool(nd['needs_rebuild'])
             for nd in nodes]
    n_theory = n_matched = n_nonthy = n_nonthy_matched = 0
    for nd in nodes:
        i = nd['node_id']
        if not needs[i]:
            continue
        tgt = nd['target']
        k = node_key(tgt, holdir)
        pri[i] = pri_log.get(k, 0.0)
        if is_theory_node(tgt):
            n_theory += 1
            if k in dur_log:
                n_matched += 1
            # only the .dat sibling carries the group's duration
            dur[i] = dur_log.get(k, default_duration) \
                     if tgt.endswith('Theory.dat') else 0.0
        else:
            n_nonthy += 1
            if k in dur_log:
                n_nonthy_matched += 1
            dur[i] = dur_log.get(k, default_duration)
    report = {
        'total_nodes': n,
        'need_rebuild': sum(1 for x in needs if x),
        'theory_rebuild': n_theory,
        'theory_matched': n_matched,
        'nonthy_rebuild': n_nonthy,
        'nonthy_matched': n_nonthy_matched,
        'default_duration': default_duration,
        'pri_entries': len(pri_log),
    }
    return pri, dur, needs, report


# --------------------------------------------------------------------
# graph structure derived once at load time

class Graph:
    """The sub-DAG of nodes needing rebuild, collapsed into *tasks*.

    Two distinct structures live here, and the difference matters:

      * Critical-path weights are computed over the RAW nodes with the
        priority costs, because that is what HM_DepGraph.compute_cp_weights
        does -- including giving each of a theory's three siblings the
        theory's full cost.  Reproducing Holmake's picker means
        reproducing its arithmetic, warts included.

      * Execution is simulated over TASKS, where a theory's siblings are
        one task: multibuild's find_nodes_by_command marks the whole
        group Succeeded from one job (multibuild.sml:435-441), so one
        job takes one duration.
    """

    def __init__(self, raw_nodes, pri, dur, needs, holdir='/repo'):
        n = len(raw_nodes)
        assert all(nd['node_id'] == i for i, nd in enumerate(raw_nodes)), \
            "node_ids are expected to be 0..n-1"
        self.targets = [nd['target'] for nd in raw_nodes]

        # ---- raw effective edges (only among nodes needing rebuild)
        raw_succs = [[] for _ in range(n)]
        raw_preds = [[] for _ in range(n)]
        for i, nd in enumerate(raw_nodes):
            if not needs[i]:
                continue
            for j in nd['dependencies']:
                if needs[j]:
                    raw_preds[i].append(j)
                    raw_succs[j].append(i)
        cp_weight = self._cp(n, raw_succs, pri, needs)

        # ---- collapse theory sibling groups into tasks
        group_of = [None] * n
        by_key = {}
        for i, nd in enumerate(raw_nodes):
            if not needs[i]:
                continue
            tgt = nd['target']
            if is_theory_node(tgt):
                gk = (nd['dir'], node_key(tgt, holdir))
                by_key.setdefault(gk, []).append(i)
            else:
                by_key[('', f'node{i}')] = [i]
        self.tasks = []          # list of member-node lists
        for gk in sorted(by_key, key=lambda k: min(by_key[k])):
            members = by_key[gk]
            group_of_id = len(self.tasks)
            for i in members:
                group_of[i] = group_of_id
            self.tasks.append(members)
        t = len(self.tasks)
        self.n = t

        # task cost = the one job's duration; task priority = the best
        # cp any member offers (all members share deps, so they become
        # runnable together)
        self.cost = [max(dur[i] for i in m) for m in self.tasks]
        self.priority = [max(cp_weight[i] for i in m)
                         for m in self.tasks]
        self.rep = [min(m) for m in self.tasks]

        preds = [set() for _ in range(t)]
        succs = [set() for _ in range(t)]
        for i in range(n):
            if not needs[i]:
                continue
            gi = group_of[i]
            for j in raw_preds[i]:
                gj = group_of[j]
                if gj != gi:
                    preds[gi].add(gj)
                    succs[gj].add(gi)
        self.indeg = [len(s) for s in preds]
        self.succs = [sorted(s) for s in succs]

        # duration-based critical path, for the lower bound
        self.cp_bound = max(self._cp(t, self.succs, self.cost,
                                     [True] * t), default=0.0)

    @staticmethod
    def _cp(n, succs, cost, needs):
        """cp[i] = cost[i] + max cp[j] over succs, by reverse topo order."""
        indeg = [0] * n
        for i in range(n):
            if not needs[i]:
                continue
            for j in succs[i]:
                indeg[j] += 1
        stack = [i for i in range(n) if needs[i] and indeg[i] == 0]
        order = []
        while stack:
            i = stack.pop()
            order.append(i)
            for j in succs[i]:
                indeg[j] -= 1
                if indeg[j] == 0:
                    stack.append(j)
        if len(order) != sum(1 for x in needs if x):
            raise RuntimeError("cycle detected in rebuild sub-DAG")
        cp = [0.0] * n
        for i in reversed(order):
            best = 0.0
            for j in succs[i]:
                if cp[j] > best:
                    best = cp[j]
            cp[i] = cost[i] + best
        return cp


# --------------------------------------------------------------------
# simulator

def simulate(g: Graph, num_workers: int, priority_fn) -> tuple[float, list]:
    """Event-driven simulation over tasks.
    priority_fn(i) -> sort key; the picker pops the ready task with
    the SMALLEST key (so negate for max-priority pickers).
    Returns (makespan, done-order)."""
    n = g.n
    remaining = list(g.indeg)
    ready = []  # min-heap of (priority, task_id)
    for i in range(n):
        if remaining[i] == 0:
            heapq.heappush(ready, (priority_fn(i), i))
    running = []  # min-heap of (completion_time, task_id)
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
    return lambda i: g.rep[i]

def picker_lpt(g: Graph):
    """Largest cost first.  Tie-break on node_id for determinism."""
    return lambda i: (-g.cost[i], g.rep[i])

def picker_hlfet(g: Graph):
    """Largest critical-path weight first.  Tie-break on node_id."""
    return lambda i: (-g.priority[i], g.rep[i])


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
          f'{coverage["need_rebuild"]} need rebuild, '
          f'{g.n} tasks after collapsing theory siblings')
    print(f'  theory nodes: {coverage["theory_rebuild"]}, '
          f'matched to duration log: {coverage["theory_matched"]} '
          f'({100 * coverage["theory_matched"] / max(1, coverage["theory_rebuild"]):.1f}%)')
    print(f'  non-theory nodes: {coverage["nonthy_rebuild"]}, '
          f'matched: {coverage["nonthy_matched"]}  '
          f'(default duration = {coverage["default_duration"]}s)')
    print(f'  priority-log entries: {coverage["pri_entries"]}')
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
        print(f'Top {top_cp} tasks by critical-path weight:')
        idxs = sorted(range(g.n), key=lambda i: -g.priority[i])[:top_cp]
        for i in idxs:
            print(f'  cp={g.priority[i]:8.1f}s  cost={g.cost[i]:7.1f}s  '
                  f'{g.targets[g.rep[i]]}')


# --------------------------------------------------------------------
# entry

def _mk(nodes, pri, dur):
    needs = [True] * len(nodes)
    return Graph(nodes, pri, dur, needs, holdir='/x')


def selftest():
    """Hand-built cases; assert HLFET beats insertion where expected."""
    # Case 1: A trivial chain X → Y where X (small) blocks Y (huge).
    # With j=2 and a bunch of small independent nodes, insertion picks the
    # small ones first, delaying Y.  HLFET sees Y downstream of X and picks
    # X immediately.
    nodes = [
        {'node_id': 0, 'target': '/x/a.uo', 'dir': '.', 'dependencies': [],
         'needs_rebuild': True},
        {'node_id': 1, 'target': '/x/b.uo', 'dir': '.', 'dependencies': [],
         'needs_rebuild': True},
        {'node_id': 2, 'target': '/x/c.uo', 'dir': '.', 'dependencies': [],
         'needs_rebuild': True},
        {'node_id': 3, 'target': '/x/d.uo', 'dir': '.', 'dependencies': [],
         'needs_rebuild': True},
        {'node_id': 4, 'target': '/x/X.uo', 'dir': '.', 'dependencies': [],
         'needs_rebuild': True},
        {'node_id': 5, 'target': '/x/Y.uo', 'dir': '.', 'dependencies': [4],
         'needs_rebuild': True},
    ]
    cost = [1.0, 1.0, 1.0, 1.0, 1.0, 100.0]
    g = _mk(nodes, cost, cost)
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

    # Case 3: blind priorities must not change durations.  Same graph,
    # zero priority information: HLFET degenerates to insertion order.
    g3 = _mk(nodes, [0.0] * 6, cost)
    blind, _ = simulate(g3, 2, picker_hlfet(g3))
    ins3,  _ = simulate(g3, 2, picker_insertion(g3))
    print(f'case 3  (j=2, blind priorities):    insertion={ins3:.1f}s  HLFET={blind:.1f}s')
    assert abs(blind - ins3) < 1e-6, \
        f'with no cost data HLFET should tie insertion, got {blind} vs {ins3}'
    assert blind > hl, 'blind HLFET should be worse than informed HLFET'

    # Case 4: a theory's three siblings are one job, not three.
    thy = [
        {'node_id': 0, 'target': '/x/fooTheory.dat', 'dir': '/x',
         'dependencies': [], 'needs_rebuild': True},
        {'node_id': 1, 'target': '/x/fooTheory.sml', 'dir': '/x',
         'dependencies': [], 'needs_rebuild': True},
        {'node_id': 2, 'target': '/x/fooTheory.sig', 'dir': '/x',
         'dependencies': [], 'needs_rebuild': True},
    ]
    gt = _mk(thy, [10.0, 10.0, 10.0], [10.0, 0.0, 0.0])
    assert gt.n == 1, f'three siblings should collapse to one task, got {gt.n}'
    mk, _ = simulate(gt, 4, picker_hlfet(gt))
    print(f'case 4  (theory siblings collapse): makespan={mk:.1f}s')
    assert abs(mk - 10.0) < 1e-6, f'one job of 10s, got {mk}'
    print('selftest OK')


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--test', action='store_true', help='run built-in selftest and exit')
    ap.add_argument('--graph', help='Holmake --json output')
    ap.add_argument('--log',   help='<key> <secs> cost data, used as '
                                    'the real durations')
    ap.add_argument('--priority-log',
                    help='cost data the scheduler sees (default: --log). '
                         'Pass /dev/null to model a cold checkout.')
    ap.add_argument('--seed', help='seed file merged under --priority-log')
    ap.add_argument('--min-cost', type=float, default=0.0,
                    help='drop seed entries below this (default 0)')
    ap.add_argument('--holdir', default='/repo',
                    help='HOL root prefix stripped from targets (default /repo)')
    ap.add_argument('-j', '--jobs', type=int, default=8, help='worker count')
    ap.add_argument('--default-duration', type=float, default=0.1,
                    help='duration (secs) for nodes with no log entry '
                         '(default 0.1).  Priorities always fall back to '
                         '0.0, as target_times.cost does.')
    ap.add_argument('--assume-all-rebuild', action='store_true',
                    help='force needs_rebuild on every node')
    ap.add_argument('--top-cp', type=int, default=0,
                    help='list top N tasks on the critical path')
    ap.add_argument('--brief', action='store_true',
                    help='one line: makespan for HLFET only')
    args = ap.parse_args()
    if args.test:
        selftest()
        return
    if not args.graph or not args.log:
        ap.error('--graph and --log are required (or use --test)')

    nodes = load_graph(args.graph)
    dur_log = load_log(args.log)
    pri_log = dict(load_log(args.seed, args.min_cost)) if args.seed else {}
    if args.priority_log:
        pri_log.update(load_log(args.priority_log))
    elif not args.seed:
        pri_log = dict(dur_log)

    pri, dur, needs, coverage = build_tables(
        nodes, pri_log, dur_log, args.holdir, args.default_duration,
        args.assume_all_rebuild)
    g = Graph(nodes, pri, dur, needs, holdir=args.holdir)

    results = {}
    for name, mk_pri in [
        ('insertion', picker_insertion),
        ('LPT', picker_lpt),
        ('HLFET', picker_hlfet),
    ]:
        makespan, _ = simulate(g, args.jobs, mk_pri(g))
        results[name] = makespan

    if args.brief:
        print(f'{results["insertion"]:.1f} {results["LPT"]:.1f} '
              f'{results["HLFET"]:.1f}')
        return

    sum_c = sum(g.cost)
    lower_bounds = {'sum_over_j': sum_c / args.jobs, 'cp': g.cp_bound}
    report(g, coverage, args.jobs, results, lower_bounds, top_cp=args.top_cp)


if __name__ == '__main__':
    main()
