#!/usr/bin/env python3
"""hmntest: parse Holmake's --json output and report what still needs building.

Run as:  hmntest.py [directory] [--holmake PATH]

`directory` defaults to the current working directory.  `--holmake`
defaults to the `bin/Holmake` of the surrounding HOL tree (walking up
from `directory` looking for `sigobj/` + `bin/Holmake`), falling back
to the binary recorded in `<directory>/.hol/make-deps/lastmaker`.

Invokes the chosen Holmake with `-C <directory> --json`, parses the
dep-graph it dumps, and prints one block per pending action: a comment
listing the files that force the rebuild, followed by the user-facing
command (a shell recipe for SomeCmd, `hol compile foo.{sml,sig}` for
BIC_Compile, `hol run fooScript.sml` for BIC_BuildScript).
"""

import argparse
import json
import os
import subprocess
import sys


def parse_command(cmd):
    """Return (kind, payload) for a JSON command string.
    kinds: 'nocmd', 'compile', 'buildscript', 'shell'."""
    if cmd == "":
        return ("nocmd", None)
    if cmd == "BIC_Compile":
        return ("compile", None)
    if cmd.startswith("BIC_Build "):
        return ("buildscript", cmd[len("BIC_Build "):])
    return ("shell", cmd)


def render_command(node):
    """Map a node to the user-facing command string, or None to skip."""
    kind, payload = parse_command(node["command"])
    if kind == "nocmd":
        return None
    if kind == "shell":
        return payload
    target = node["target"]
    base = os.path.basename(target)
    if kind == "compile":
        stem, ext = os.path.splitext(base)
        if ext == ".ui":
            return f"hol compile {stem}.sig"
        if ext == ".uo":
            return f"hol compile {stem}.sml"
        return f"hol compile {base}"  # fallback for unexpected extensions
    if kind == "buildscript":
        script_base = os.path.basename(payload)
        return f"hol run {script_base}Script.sml"
    raise AssertionError(f"unhandled kind: {kind}")


def forcing_files(node, by_id):
    """Set of dep targets (or sentinel strings) that force N's rebuild."""
    forced = set()
    if node["mtime"] is None and not node["phony"]:
        forced.add("<target nonexistent>")
    n_mtime = node["mtime"]
    for dep_id in node["dependencies"]:
        dep = by_id[dep_id]
        if dep["phony"]:
            continue
        if dep["needs_rebuild"]:
            forced.add(dep["target"])
            continue
        d_mtime = dep["mtime"]
        if d_mtime is not None and n_mtime is not None and d_mtime > n_mtime:
            forced.add(dep["target"])
    return forced


def dedup_key(node):
    """Two needs-rebuild nodes that should merge into one output block
    share this key.  For BIC_BuildScript, dedupe by the script path.
    For SomeCmd, dedupe by the verbatim command string.  Everything
    else stays per-node (each .ui / .uo / phony NoCmd warning prints
    on its own)."""
    kind, payload = parse_command(node["command"])
    if kind == "buildscript":
        return ("buildscript", payload)
    if kind == "shell":
        return ("shell", payload)
    return ("node", node["node_id"])


def topo_order(pending_ids, by_id):
    """Post-order DFS over the pending-only subgraph; returns a list of
    node ids in build order (deps first)."""
    pending = set(pending_ids)
    order = []
    visited = set()

    def visit(nid):
        if nid in visited:
            return
        visited.add(nid)
        node = by_id[nid]
        for d in node["dependencies"]:
            if d in pending:
                visit(d)
        order.append(nid)

    for nid in sorted(pending):
        visit(nid)
    return order


def find_holmake(directory):
    """Resolve a Holmake binary for `directory`.

    Walks up from `directory` looking for a HOL tree root (`sigobj/`
    plus `bin/Holmake`, the same marker Holmake's own check_distrib
    uses).  Falls back to the binary recorded in
    `<directory>/.hol/make-deps/lastmaker`.  Returns an absolute path
    on success, None on failure.
    """
    d = os.path.abspath(directory)
    while True:
        sigobj = os.path.join(d, "sigobj")
        holmake = os.path.join(d, "bin", "Holmake")
        if (os.path.isdir(sigobj)
                and os.access(sigobj, os.R_OK | os.X_OK)
                and os.path.isfile(holmake)
                and os.access(holmake, os.R_OK | os.X_OK)):
            return holmake
        parent = os.path.dirname(d)
        if parent == d:
            break
        d = parent

    lastmaker = os.path.join(
        os.path.abspath(directory), ".hol", "make-deps", "lastmaker"
    )
    if os.path.isfile(lastmaker):
        try:
            with open(lastmaker) as f:
                first = f.readline().rstrip()
        except OSError:
            return None
        if first:
            return first
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("directory", nargs="?", default=os.getcwd(),
                    help="directory to run Holmake in (default: cwd)")
    ap.add_argument("--holmake", "-H", default=None,
                    help="path to the Holmake executable (default: "
                         "scan up from <directory> for bin/Holmake, "
                         "then consult .hol/make-deps/lastmaker)")
    args = ap.parse_args()

    holmake = args.holmake or find_holmake(args.directory)
    if holmake is None:
        print(f"hmntest: could not locate a Holmake binary for "
              f"{args.directory!r}; pass --holmake explicitly",
              file=sys.stderr)
        return 1

    try:
        result = subprocess.run(
            [holmake, "-C", args.directory, "--json"],
            capture_output=True, text=True, check=True,
        )
    except FileNotFoundError:
        print(f"hmntest: holmake not found: {holmake}", file=sys.stderr)
        return 1
    except PermissionError:
        print(f"hmntest: holmake not executable: {holmake}", file=sys.stderr)
        return 1
    except OSError as e:
        print(f"hmntest: cannot exec {holmake}: {e}\n"
              f"  (possible architecture mismatch; pass --holmake to override)",
              file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as e:
        sys.stderr.write(e.stderr)
        print(f"hmntest: holmake exited {e.returncode}", file=sys.stderr)
        return 1

    try:
        graph = json.loads(result.stdout)
    except json.JSONDecodeError as e:
        print(f"hmntest: JSON parse failed: {e}", file=sys.stderr)
        print(f"first 200 chars of stdout: {result.stdout[:200]!r}",
              file=sys.stderr)
        return 1

    by_id = {n["node_id"]: n for n in graph}
    pending_ids = [n["node_id"] for n in graph if n["needs_rebuild"]]
    if not pending_ids:
        print("# (nothing to build)")
        return 0

    # Group pending nodes into output blocks by dedup_key.
    blocks = {}  # key -> {"forced": set, "cmd_node": node, "ids": [ids]}
    nocmd_warnings = []  # list of (target,) for NoCmd-but-needed nodes

    for nid in pending_ids:
        node = by_id[nid]
        if node["phony"]:
            continue
        kind, _ = parse_command(node["command"])
        if kind == "nocmd":
            nocmd_warnings.append(node["target"])
            continue
        key = dedup_key(node)
        entry = blocks.setdefault(
            key, {"forced": set(), "cmd_node": node, "ids": []}
        )
        entry["forced"] |= forcing_files(node, by_id)
        entry["ids"].append(nid)

    # Topo-sort the blocks by their representative node's position.
    block_keys = list(blocks.keys())
    if block_keys:
        rep_id_for_key = {
            k: min(blocks[k]["ids"]) for k in block_keys
        }
        topo = topo_order(
            [rep_id_for_key[k] for k in block_keys], by_id
        )
        topo_index = {nid: i for i, nid in enumerate(topo)}
        block_keys.sort(
            key=lambda k: (topo_index.get(rep_id_for_key[k], -1),
                           render_command(blocks[k]["cmd_node"]) or "")
        )

    for target in sorted(set(nocmd_warnings)):
        print(f"# WARNING: no rule for {target} (needs rebuild)")

    first = (len(nocmd_warnings) == 0)
    for key in block_keys:
        entry = blocks[key]
        cmd = render_command(entry["cmd_node"])
        forced = entry["forced"]
        if not forced:
            forced = {"<cachekey or non-direct cause>"}
        if not first:
            print()
        first = False
        print(f"# Because: {', '.join(sorted(forced))}")
        print(cmd)
    return 0


if __name__ == "__main__":
    sys.exit(main())
