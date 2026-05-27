#!/usr/bin/env python3
"""Fuzz-tester for HOL4's Holmake incremental machinery.

Repeatedly snapshots a set of source trees plus the Holmake product
cache, applies a small set of file mutations (delete a build product,
touch a source file, remove a cache entry, prepend a comment to a
source file), then runs Holmake and checks that the rebuild succeeds.

A failed rebuild is preserved (manifest + snapshot + holmake log) under
``<tmp>/failures/<id>/`` for triage; the live trees are restored from
the snapshot before the next round, so a long unattended session
accumulates triagable failures without permanently corrupting the
working state.

See ``developers/fuzz_holmake.py --help`` for the CLI.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import random
import shutil
import signal
import subprocess
import sys
import time
from dataclasses import dataclass, field
from itertools import chain
from pathlib import Path
from typing import Iterable


# ── classification rules ─────────────────────────────────────────────

SOURCE_EXTS = {".sml", ".sig"}                       # source files
BUILD_PRODUCT_EXTS = {".ui", ".uo", ".dat", ".cachekey"}
HOL_OBJDIRS = {".hol", ".HOLMK"}                      # any dir name here ⇒ build area
SKIP_DIRS = {".git", "papers", "dump"}                # never walked at all
BACKUP_SUFFIXES = ("~",)                              # *~ Emacs backups

DEFAULT_WEIGHTS = {
    "rm-product":   8,
    "touch-source": 8,
    "rm-cache":     6,
    "edit-source":  8,
}
DEFAULT_MUTATIONS = sum(DEFAULT_WEIGHTS.values())     # 30


# ── interrupt handling ───────────────────────────────────────────────
#
# Ctrl-C (SIGINT)  -> abort the *current* round; treated as a failure
#                     (snapshot + manifest + log preserved, live trees
#                     restored from snap, fuzzer continues with the
#                     next round).
# Ctrl-\  (SIGQUIT) -> abort the *whole* campaign; the current round
#                     is torn down the same way, then the main loop
#                     exits before starting the next round.

_interrupted = {"round": False, "campaign": False}
_current_proc: list = [None]  # single-slot mutable holder for the running Popen


def _kill_current_proc() -> None:
    p = _current_proc[0]
    if p is not None:
        try:
            p.terminate()
        except ProcessLookupError:
            pass


def _on_sigint(signum, frame) -> None:
    _interrupted["round"] = True
    _kill_current_proc()


def _on_sigquit(signum, frame) -> None:
    _interrupted["campaign"] = True
    _kill_current_proc()


def install_signal_handlers() -> None:
    signal.signal(signal.SIGINT, _on_sigint)
    if hasattr(signal, "SIGQUIT"):
        signal.signal(signal.SIGQUIT, _on_sigquit)


# ── small utilities ──────────────────────────────────────────────────

def short_token(rng: random.Random) -> str:
    """A short URL-safe random token used as a run id."""
    alphabet = "abcdefghijklmnopqrstuvwxyz0123456789"
    return "".join(rng.choice(alphabet) for _ in range(8))


def is_inside(p: Path, root: Path) -> bool:
    return p.resolve().is_relative_to(root.resolve())


# ── snapshot probe ───────────────────────────────────────────────────

def probe_snapshot_method(probe_dir: Path) -> str:
    """Return one of 'cp-c', 'reflink', 'rsync'.

    Probes by attempting a tiny clone inside ``probe_dir``. The choice
    is logged so the user can tell whether they're on the fast path.
    """
    probe_dir.mkdir(parents=True, exist_ok=True)
    src = probe_dir / "_probe_src"
    dst = probe_dir / "_probe_dst"
    shutil.rmtree(src, ignore_errors=True)
    shutil.rmtree(dst, ignore_errors=True)
    src.mkdir()
    (src / "f.txt").write_text("probe\n")

    def _try(cmd: list[str]) -> bool:
        shutil.rmtree(dst, ignore_errors=True)
        return subprocess.run(cmd, capture_output=True).returncode == 0

    if platform.system() == "Darwin" and _try(["cp", "-c", "-R", str(src), str(dst)]):
        chosen = "cp-c"
    elif _try(["cp", "--reflink=always", "-R", str(src), str(dst)]):
        chosen = "reflink"
    else:
        chosen = "rsync"

    shutil.rmtree(src, ignore_errors=True)
    shutil.rmtree(dst, ignore_errors=True)
    return chosen


def clone_tree(src: Path, dst: Path, method: str) -> None:
    """Clone ``src`` to ``dst`` using the chosen method. ``dst`` must not exist."""
    if dst.exists():
        raise RuntimeError(f"clone destination already exists: {dst}")
    dst.parent.mkdir(parents=True, exist_ok=True)

    if method == "cp-c":
        cmd = ["cp", "-c", "-R", str(src), str(dst)]
    elif method == "reflink":
        cmd = ["cp", "--reflink=always", "-R", str(src), str(dst)]
    elif method == "rsync":
        dst.mkdir(parents=True, exist_ok=True)
        cmd = ["rsync", "-a", f"{src}/", f"{dst}/"]
    else:
        raise ValueError(f"unknown snapshot method: {method}")

    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(
            f"clone {src} -> {dst} via {method} failed: {r.stderr.strip() or r.stdout.strip()}"
        )


def restore_tree(snap: Path, live: Path, method: str) -> None:
    """Restore ``live`` to match ``snap`` exactly (byte-identical).

    On COW filesystems (``cp-c`` / ``reflink``) the restore is just
    ``rm -rf live; clone snap -> live`` — fast and unambiguous.

    On the rsync fallback we use ``rsync -a --delete --checksum``;
    the checksum compare is necessary because macOS rsync defaults
    to second-resolution mtime comparison, so a mutation applied
    within the same wall-clock second as the snapshot can produce
    identical (size, truncated-mtime) yet differing content.
    """
    if not snap.exists():
        raise RuntimeError(f"snapshot missing: {snap}")

    if method in ("cp-c", "reflink"):
        shutil.rmtree(live, ignore_errors=True)
        clone_tree(snap, live, method)
        return

    # rsync fallback
    live.mkdir(parents=True, exist_ok=True)
    cmd = ["rsync", "-a", "--delete", "--checksum", f"{snap}/", f"{live}/"]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(
            f"restore {snap} -> {live} failed: {r.stderr.strip() or r.stdout.strip()}"
        )


# ── tree population (source / build-product / meta) ──────────────────

def _walks_skip(name: str) -> bool:
    return name in SKIP_DIRS or name.endswith(BACKUP_SUFFIXES)


def _under_hol_objdir(rel: Path) -> bool:
    return any(part in HOL_OBJDIRS for part in rel.parts)


def _holmake_visited(d: Path) -> bool:
    """True iff Holmake has visited ``d`` (non-empty .hol/make-deps).

    Restricts the mutation population to source files Holmake actually
    cares about for this build: a directory that contains no Holmake
    dep cache wasn't entered during the build and its .sml/.sig files
    can't influence the outcome. Excludes unrelated sub-projects
    (e.g. tools/Holmake/tests/<fixture>/) when fuzzing under HOL's
    checkout.
    """
    mdir = d / ".hol" / "make-deps"
    if not mdir.is_dir():
        return False
    return any(mdir.iterdir())


@dataclass
class TreePopulation:
    sources:        list[Path] = field(default_factory=list)
    build_products: list[Path] = field(default_factory=list)


def classify_tree(root: Path) -> TreePopulation:
    """Walk ``root`` once, bucketing files into sources / build products.

    Sources are only collected from directories Holmake has visited
    (per ``_holmake_visited``); build products are collected from any
    ``.hol/objs``-style area regardless. Holmakefile mutation is
    intentionally out-of-scope: failures would blur into makefile
    parser quirks rather than telling us anything about Holmake's
    incremental machinery, and the existing ``lastmaker_propagation``
    test already covers the re-read path.
    """
    pop = TreePopulation()
    if not root.exists():
        return pop
    root = root.resolve()

    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if not _walks_skip(d)]

        cur = Path(dirpath)
        rel_dir = cur.relative_to(root) if cur != root else Path()
        in_build_area = _under_hol_objdir(rel_dir)
        visited = in_build_area or _holmake_visited(cur)

        for fn in filenames:
            if fn.endswith(BACKUP_SUFFIXES):
                continue
            p = cur / fn
            suffix = p.suffix

            if in_build_area or suffix in BUILD_PRODUCT_EXTS:
                pop.build_products.append(p)
            elif visited and suffix in SOURCE_EXTS:
                pop.sources.append(p)
            # else: not in a Holmake-visited dir; skip as not-relevant

    return pop


def enumerate_cache(cache_dir: Path) -> list[Path]:
    """Return all deletable cache entries (key/* and data/*)."""
    out: list[Path] = []
    for sub in ("key", "data"):
        d = cache_dir / sub
        if d.is_dir():
            for entry in d.iterdir():
                if entry.is_file():
                    out.append(entry)
    return out


# ── mutation operations ──────────────────────────────────────────────

def _prepend_fuzz_comment(p: Path, token: str) -> None:
    """Prepend a one-line ML comment to a source file (byte-safe)."""
    data = p.read_bytes()
    header = f"(* fuzz {token} *)\n".encode("utf-8")
    p.write_bytes(header + data)


def apply_mutation(p: Path, kind: str, token: str) -> dict:
    """Apply one mutation; return a manifest entry."""
    entry = {
        "path": str(p),
        "kind": kind,
        "ts":   time.time(),
    }
    if kind in ("rm-product", "rm-cache"):
        entry["was_absent"] = not p.exists()
        p.unlink(missing_ok=True)
    elif kind == "touch-source":
        os.utime(p, None)
    elif kind == "edit-source":
        _prepend_fuzz_comment(p, token)
    else:
        raise ValueError(f"unknown mutation kind: {kind}")
    return entry


# ── mutation planning ────────────────────────────────────────────────

def plan_mutations(
    rng:          random.Random,
    populations:  dict[Path, TreePopulation],
    cache_files:  list[Path],
    total:        int,
    weights:      dict[str, int],
) -> list[tuple[Path, str]]:
    """Choose ``total`` (path, kind) pairs to mutate.

    Distributes counts proportionally to ``weights``; samples paths
    without replacement from each kind's eligible population.
    """
    wsum = sum(weights.values())
    counts: dict[str, int] = {}
    remaining = total
    kinds = list(weights.keys())
    for i, k in enumerate(kinds):
        if i == len(kinds) - 1:
            counts[k] = remaining
        else:
            n = round(total * weights[k] / wsum)
            counts[k] = n
            remaining -= n

    plan: list[tuple[Path, str]] = []
    used: set[Path] = set()

    def pick(pool: list[Path], k: int) -> list[Path]:
        candidates = [p for p in pool if p not in used]
        rng.shuffle(candidates)
        chosen = candidates[:k]
        used.update(chosen)
        return chosen

    source_pool = list(chain.from_iterable(pop.sources for pop in populations.values()))
    product_pool = list(chain.from_iterable(pop.build_products for pop in populations.values()))

    for p in pick(product_pool, counts["rm-product"]):
        plan.append((p, "rm-product"))
    for p in pick(source_pool, counts["touch-source"]):
        plan.append((p, "touch-source"))
    for p in pick(list(cache_files), counts["rm-cache"]):
        plan.append((p, "rm-cache"))
    for p in pick(source_pool, counts["edit-source"]):
        plan.append((p, "edit-source"))

    rng.shuffle(plan)
    return plan


# ── round driver ─────────────────────────────────────────────────────

@dataclass
class Config:
    master_dir:     Path
    trees:          list[Path]
    cache_dir:      Path
    tmp_dir:        Path
    holmake:        Path
    runs:           int
    mutations:      int
    seed:           int
    jobs:           int
    target:         str | None
    on_failure:     str
    weights:        dict[str, int]
    no_cache_prob:  float = 0.5
    quiet:          bool = False
    holdir:         Path | None = None
    resume_id:      str | None = None
    snap_method:    str = "rsync"


def tree_token(t: Path, taken: set[str]) -> str:
    base = t.name or "root"
    if base not in taken:
        return base
    h = hashlib.sha1(str(t.resolve()).encode()).hexdigest()[:6]
    return f"{base}-{h}"


def tree_tokens_for(trees: list[Path]) -> dict[Path, str]:
    taken: set[str] = set()
    mapping: dict[Path, str] = {}
    for t in trees:
        tok = tree_token(t, taken)
        taken.add(tok)
        mapping[t] = tok
    return mapping


# ── starting-state snapshot (restored on exit) ───────────────────────

def _starting_state_dir(cfg: "Config") -> Path:
    return cfg.tmp_dir / "starting_state"


def snapshot_starting_state(cfg: "Config") -> None:
    """Snapshot every --tree + cache_dir BEFORE anything mutates them.

    Restored on fuzzer exit (natural, --on-failure stop, SIGQUIT, or
    Python exception), so the user's working checkouts end the
    session exactly as they began it. Snapshotting before
    clean_make_deps and before the baseline build means the user
    lands back at their pre-fuzz state, not the post-baseline-build
    state.
    """
    snap = _starting_state_dir(cfg)
    if snap.exists():
        shutil.rmtree(snap)
    snap.mkdir(parents=True)
    for t, tok in tree_tokens_for(cfg.trees).items():
        clone_tree(t, snap / tok, cfg.snap_method)
    clone_tree(cfg.cache_dir, snap / "_cache", cfg.snap_method)


def restore_starting_state(cfg: "Config") -> None:
    snap = _starting_state_dir(cfg)
    if not snap.exists():
        return
    print("[fuzz] restoring trees + cache to pre-fuzz state ...")
    try:
        for t, tok in tree_tokens_for(cfg.trees).items():
            tree_snap = snap / tok
            if tree_snap.exists():
                restore_tree(tree_snap, t, cfg.snap_method)
        cache_snap = snap / "_cache"
        if cache_snap.exists():
            restore_tree(cache_snap, cfg.cache_dir, cfg.snap_method)
    except Exception as e:
        print(f"[fuzz] WARN: restore failed: {e}", file=sys.stderr)


def _stream_with_pty(cmd: list[str], cwd: str, log_path: Path) -> int:
    """Run cmd in a pty so it sees a TTY; tee output to stdout + log.

    Lets Holmake emit its native TTY status line (overwriting via
    ``\\r``) into the user's terminal while a full copy of the
    output -- including the in-place overwrites -- still lands in
    the log file for triage.
    """
    import pty
    master_fd, slave_fd = pty.openpty()
    with log_path.open("wb") as logf:
        logf.write((" ".join(cmd) + "\n").encode())
        logf.flush()
        proc = subprocess.Popen(
            cmd, cwd=cwd,
            stdin=slave_fd, stdout=slave_fd, stderr=slave_fd,
            close_fds=True,
        )
        _current_proc[0] = proc
        os.close(slave_fd)
        try:
            while True:
                try:
                    data = os.read(master_fd, 4096)
                except OSError:
                    break
                if not data:
                    break
                logf.write(data); logf.flush()
                sys.stdout.buffer.write(data); sys.stdout.buffer.flush()
        finally:
            try:
                os.close(master_fd)
            except OSError:
                pass
            _current_proc[0] = None
        proc.wait()
        # leave a clean line after Holmake's last \r-overwrite
        sys.stdout.write("\n"); sys.stdout.flush()
        return proc.returncode


def run_holmake(cfg: Config, log_path: Path, no_cache: bool = False) -> int:
    cmd = [str(cfg.holmake), f"-j{cfg.jobs}"]
    if no_cache:
        cmd.append("--no-cache")
    else:
        cmd.append(f"--cache-dir={cfg.cache_dir}")
    if cfg.target:
        cmd.append(cfg.target)
    log_path.parent.mkdir(parents=True, exist_ok=True)

    if not cfg.quiet and sys.stdout.isatty():
        return _stream_with_pty(cmd, str(cfg.master_dir), log_path)

    with log_path.open("wb") as logf:
        logf.write((" ".join(cmd) + "\n").encode())
        logf.flush()
        proc = subprocess.Popen(cmd, cwd=str(cfg.master_dir),
                                stdout=logf, stderr=subprocess.STDOUT)
        _current_proc[0] = proc
        try:
            proc.wait()
        finally:
            _current_proc[0] = None
    return proc.returncode


def baseline(cfg: Config) -> int:
    log = cfg.tmp_dir / "baseline.log"
    print(f"[fuzz] baseline build: {cfg.holmake} (cwd={cfg.master_dir}, cache={cfg.cache_dir})")
    rc = run_holmake(cfg, log)
    if rc != 0:
        print(f"[fuzz] baseline build FAILED (rc={rc}); log at {log}")
    else:
        print("[fuzz] baseline build OK")
    return rc


def clean_make_deps(trees: list[Path]) -> int:
    """Wipe every ``.hol/make-deps/`` under each tree.

    The baseline Holmake invocation regenerates them; the wipe
    ensures the visited-dir analysis used by ``classify_tree`` sees
    only directories Holmake entered for *this* build, not stale
    state from past unrelated builds in the same trees.
    """
    removed = 0
    for tree in trees:
        if not tree.is_dir():
            continue
        for mdir in tree.rglob(".hol/make-deps"):
            if mdir.is_dir():
                shutil.rmtree(mdir, ignore_errors=True)
                removed += 1
    return removed


def detect_missing_trees(cfg: Config) -> None:
    """Warn for dirs that Holmake depends on but the user didn't list."""
    seen_dirs: set[Path] = set()
    for t in cfg.trees + [cfg.master_dir]:
        depdir = t / ".hol" / "make-deps"
        if not depdir.is_dir():
            continue
        for dfile in depdir.glob("*.d"):
            try:
                for line in dfile.read_text().splitlines():
                    for tok in line.split():
                        if tok.startswith("/"):
                            d = Path(tok).parent
                            seen_dirs.add(d)
            except OSError:
                continue
    tree_roots = [t.resolve() for t in cfg.trees]
    warned: set[Path] = set()
    for d in seen_dirs:
        if any(is_inside(d, r) for r in tree_roots):
            continue
        if d in warned:
            continue
        warned.add(d)
        print(
            f"WARN: Holmake depends on files under {d} but no --tree covers it.\n"
            f"      Add `--tree {d}` to snapshot and fuzz that dir."
        )


def do_round(cfg: Config, rng: random.Random, run_idx: int) -> tuple[bool, str, bool]:
    """Run one fuzz round. Returns (success?, run_id, no_cache?)."""
    _interrupted["round"] = False  # reset; campaign flag carries across rounds
    run_id = short_token(rng)
    run_dir = cfg.tmp_dir / "runs" / run_id
    run_dir.mkdir(parents=True)
    snap_root = run_dir / "snap"
    snap_root.mkdir()

    # snapshot every tree + cache
    taken: set[str] = set()
    tree_tokens: dict[Path, str] = {}
    for t in cfg.trees:
        tok = tree_token(t, taken)
        taken.add(tok)
        tree_tokens[t] = tok
        clone_tree(t, snap_root / tok, cfg.snap_method)
    clone_tree(cfg.cache_dir, snap_root / "cache", cfg.snap_method)

    # classify after snapshot (so mutations don't leak into the snap)
    populations = {t: classify_tree(t) for t in cfg.trees}
    cache_files = enumerate_cache(cfg.cache_dir)

    plan = plan_mutations(
        rng=rng,
        populations=populations,
        cache_files=cache_files,
        total=cfg.mutations,
        weights=cfg.weights,
    )
    no_cache = rng.random() < cfg.no_cache_prob

    token = run_id
    manifest = {
        "run_id":  run_id,
        "seed":    cfg.seed,
        "round":   run_idx,
        "snap_method": cfg.snap_method,
        "trees":   {str(t): tree_tokens[t] for t in cfg.trees},
        "cache":   str(cfg.cache_dir),
        "weights": cfg.weights,
        "no_cache": no_cache,
        "mutations": [],
    }

    for p, kind in plan:
        try:
            entry = apply_mutation(p, kind, token)
        except OSError as e:
            entry = {"path": str(p), "kind": kind, "ts": time.time(), "error": str(e)}
        manifest["mutations"].append(entry)

    (run_dir / "manifest.json").write_text(json.dumps(manifest, indent=2))

    if not cfg.quiet:
        cache_tag = "no-cache" if no_cache else "cached"
        print(f"[fuzz] round {run_idx}/{cfg.runs} ({run_id}, {cache_tag}) -- "
              f"{len(manifest['mutations'])} mutations:")
        for entry in manifest["mutations"]:
            note = ""
            if entry.get("was_absent"):
                note = "  (was absent)"
            elif "error" in entry:
                note = f"  (error: {entry['error']})"
            print(f"  {entry['kind']:13}  {entry['path']}{note}")

    rc = run_holmake(cfg, run_dir / "holmake.log", no_cache=no_cache)

    interrupted = "campaign" if _interrupted["campaign"] \
                  else "round" if _interrupted["round"] else None

    if rc == 0 and not interrupted:
        # drop the snapshot; the live trees are now a fresh baseline
        shutil.rmtree(run_dir)
        return True, run_id, no_cache

    # failure path (real build failure or user-interrupt)
    fail_dir = cfg.tmp_dir / "failures" / run_id
    err = _first_error_line(run_dir / "holmake.log")
    if interrupted:
        err = f"interrupted by user ({interrupted})"
        manifest["interrupted"] = interrupted
        (run_dir / "manifest.json").write_text(json.dumps(manifest, indent=2))
    if cfg.on_failure in ("restore-and-continue", "stop"):
        for t in cfg.trees:
            restore_tree(snap_root / tree_tokens[t], t, cfg.snap_method)
        restore_tree(snap_root / "cache", cfg.cache_dir, cfg.snap_method)

    fail_dir.parent.mkdir(parents=True, exist_ok=True)
    shutil.move(str(run_dir), str(fail_dir))

    idx = cfg.tmp_dir / "failures" / "index.log"
    with idx.open("a") as fh:
        fh.write(
            f"{run_id}  seed={cfg.seed}  round={run_idx}  "
            f"mutations={len(manifest['mutations'])}  "
            f"no_cache={no_cache}  "
            f"interrupted={interrupted or 'no'}  "
            f"first_error={err}\n"
        )

    if interrupted:
        print(f"[fuzz] INTERRUPTED ({interrupted}) in round {run_idx} "
              f"(id={run_id}); preserved at {fail_dir}")
    else:
        print(f"[fuzz] FAILURE in round {run_idx} "
              f"(id={run_id}); preserved at {fail_dir}")
    return False, run_id, no_cache


def _first_error_line(log_path: Path) -> str:
    fallback = ""
    try:
        with log_path.open("r", errors="replace") as fh:
            for line in fh:
                low = line.lower()
                if "error" in low or "failed" in low or "cannot" in low:
                    return line.strip()[:200]
                if not fallback and line.strip():
                    fallback = line.strip()[:200]
    except OSError:
        return "(log unreadable)"
    return fallback


# ── argv parsing ─────────────────────────────────────────────────────

def find_holmake(arg: str | None) -> Path:
    if arg:
        p = Path(arg).expanduser().resolve()
        if not p.exists():
            raise SystemExit(f"--holmake {p} does not exist")
        return p
    holdir = os.environ.get("HOLDIR")
    if holdir:
        cand = Path(holdir).expanduser() / "bin" / "Holmake"
        if cand.exists():
            return cand.resolve()
    found = shutil.which("Holmake")
    if found:
        return Path(found).resolve()
    raise SystemExit(
        "Cannot locate Holmake. Set $HOLDIR or pass --holmake PATH."
    )


def derive_holdir(holmake: Path) -> Path:
    return holmake.resolve().parent.parent


def default_trees(master: Path, holdir: Path) -> list[Path]:
    """Default tree set: master dir + HOL4 dir, deduplicated."""
    seen: list[Path] = []
    for t in (master, holdir):
        r = t.resolve()
        if r not in [s.resolve() for s in seen]:
            seen.append(r)
    return seen


def default_tmp_dir(master: Path) -> Path:
    """Per-master scratch under ~/.cache/fuzz_holmake/.

    Must live OUTSIDE the master tree: the restore path is
    "rm -rf live; clone snap -> live", so anything under master gets
    nuked along with the live tree and the clone has nothing to
    read.
    """
    h = hashlib.sha1(str(master.resolve()).encode()).hexdigest()[:8]
    return Path.home() / ".cache" / "fuzz_holmake" / f"{master.name}-{h}"


def _check_outside_trees(label: str, d: Path, trees: list[Path]) -> None:
    for t in trees:
        if is_inside(d, t):
            raise SystemExit(
                f"--{label} {d} is inside --tree {t}.\n"
                f"  Snapshot+restore nukes the live tree before cloning "
                f"the snap back; if the snap lives inside the tree, the "
                f"snap gets nuked too.\n"
                f"  Pick a --{label} outside every --tree."
            )


def parse_args(argv: list[str]) -> Config:
    ap = argparse.ArgumentParser(
        description="Fuzz-test Holmake's incremental build machinery.",
        epilog="With no arguments, fuzzes the cwd against HOL4 (via $HOLDIR / "
               "`which Holmake`) using script-private cache and tmp dirs.",
    )
    ap.add_argument("--master-dir", type=Path, default=Path.cwd(),
                    help="Where Holmake runs (default: cwd).")
    ap.add_argument("--tree", action="append", type=Path, default=[],
                    metavar="PATH",
                    help="Repeatable. Source trees to snapshot+fuzz. "
                         "Default: [master-dir, HOLDIR].")
    ap.add_argument("--cache-dir", type=Path, default=None,
                    help="Holmake --cache-dir. Default: <tmp-dir>/cache.")
    ap.add_argument("--tmp-dir", type=Path, default=None,
                    help="Snapshot + failure storage root. "
                         "Default: ~/.cache/fuzz_holmake/<master>-<hash>/. "
                         "Must live outside every --tree.")
    ap.add_argument("--holmake", type=str, default=None,
                    help="Path to Holmake binary. Default: $HOLDIR/bin/Holmake "
                         "or `which Holmake`.")
    ap.add_argument("--runs", type=int, default=50)
    ap.add_argument("--mutations", type=int, default=DEFAULT_MUTATIONS)
    ap.add_argument("--seed", type=int, default=None)
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--target", type=str, default=None)
    ap.add_argument("--no-cache-prob", type=float, default=0.5,
                    metavar="P",
                    help="Probability (0..1) that a round invokes Holmake "
                         "with --no-cache. Default 0.5; set 0 to always use "
                         "the cache, 1 to never use it.")
    ap.add_argument("--on-failure", choices=["restore-and-continue", "stop", "preserve"],
                    default="restore-and-continue")
    ap.add_argument("--quiet", "-q", action="store_true",
                    help="Suppress per-round mutation listing and pass-through "
                         "of Holmake's TTY output; keep just the one-line "
                         "round summary.")
    ap.add_argument("--resume", type=str, default=None, metavar="<id>",
                    help="Restore live trees from a saved failure run, then exit.")

    args = ap.parse_args(argv)

    master = args.master_dir.expanduser().resolve()
    if not master.is_dir():
        raise SystemExit(f"--master-dir {master} is not a directory")

    holmake = find_holmake(args.holmake)
    holdir = derive_holdir(holmake)

    trees = [t.expanduser().resolve() for t in args.tree] or default_trees(master, holdir)
    # master must be covered for cache walk; if not, prepend it
    if not any(is_inside(master, t) for t in trees):
        trees = [master] + trees

    tmp_dir = (args.tmp_dir or default_tmp_dir(master)).expanduser().resolve()
    cache_dir = (args.cache_dir or (tmp_dir / "cache")).expanduser().resolve()

    _check_outside_trees("tmp-dir", tmp_dir, trees)
    _check_outside_trees("cache-dir", cache_dir, trees)

    # refuse to clobber the global default cache
    shared = (Path.home() / ".cache" / "HOL").resolve()
    if cache_dir == shared:
        raise SystemExit(
            f"--cache-dir {cache_dir} would corrupt the global HOL cache. "
            "Pick a script-private path."
        )

    seed = args.seed if args.seed is not None else int(time.time())

    if not 0.0 <= args.no_cache_prob <= 1.0:
        raise SystemExit("--no-cache-prob must be in [0, 1]")

    return Config(
        master_dir=master,
        trees=trees,
        cache_dir=cache_dir,
        tmp_dir=tmp_dir,
        holmake=holmake,
        runs=args.runs,
        mutations=args.mutations,
        seed=seed,
        jobs=args.jobs,
        target=args.target,
        on_failure=args.on_failure,
        weights=dict(DEFAULT_WEIGHTS),
        no_cache_prob=args.no_cache_prob,
        quiet=args.quiet,
        holdir=holdir,
        resume_id=args.resume,
    )


# ── main ─────────────────────────────────────────────────────────────

def setup_dirs(cfg: Config) -> None:
    cfg.tmp_dir.mkdir(parents=True, exist_ok=True)
    cfg.cache_dir.mkdir(parents=True, exist_ok=True)


def resume(cfg: Config, run_id: str) -> int:
    fail_dir = cfg.tmp_dir / "failures" / run_id
    if not fail_dir.is_dir():
        raise SystemExit(f"no failure dir at {fail_dir}")
    manifest_path = fail_dir / "manifest.json"
    if not manifest_path.exists():
        raise SystemExit(f"{manifest_path} missing")
    manifest = json.loads(manifest_path.read_text())
    tree_tokens = manifest["trees"]
    snap_root = fail_dir / "snap"
    method = manifest.get("snap_method", "rsync")
    for tree_path_str, tok in tree_tokens.items():
        restore_tree(snap_root / tok, Path(tree_path_str), method)
    restore_tree(snap_root / "cache", Path(manifest["cache"]), method)
    print(f"[fuzz] restored live trees from failures/{run_id}/")
    return 0


def main(argv: list[str]) -> int:
    cfg = parse_args(argv)
    setup_dirs(cfg)
    install_signal_handlers()

    if cfg.resume_id:
        return resume(cfg, cfg.resume_id)

    cfg.snap_method = probe_snapshot_method(cfg.tmp_dir / "_probe")
    print(f"[fuzz] snapshot method: {cfg.snap_method}")
    if cfg.snap_method == "rsync":
        print("[fuzz] WARN: COW clone unavailable on this filesystem; "
              "rsync fallback will be slow on large trees.")

    print(f"[fuzz] master-dir   = {cfg.master_dir}")
    print(f"[fuzz] trees        = {[str(t) for t in cfg.trees]}")
    print(f"[fuzz] holmake      = {cfg.holmake}")
    print(f"[fuzz] cache-dir    = {cfg.cache_dir}")
    print(f"[fuzz] tmp-dir      = {cfg.tmp_dir}")
    print(f"[fuzz] runs={cfg.runs} mutations={cfg.mutations} jobs={cfg.jobs} "
          f"no_cache_prob={cfg.no_cache_prob}")
    print(f"[fuzz] seed         = {cfg.seed}")
    print(f"[fuzz] interrupts   = Ctrl-C fails current round; "
          f"Ctrl-\\ aborts the campaign")

    print("[fuzz] snapping starting state (restored on exit) ...")
    snapshot_starting_state(cfg)

    try:
        n = clean_make_deps(cfg.trees)
        print(f"[fuzz] cleared {n} stale .hol/make-deps/ dir(s) before baseline")

        rc = baseline(cfg)
        if rc != 0:
            return rc

        detect_missing_trees(cfg)

        rng = random.Random(cfg.seed)
        failures = 0
        for i in range(1, cfg.runs + 1):
            ok, run_id, no_cache = do_round(cfg, rng, i)
            status = "OK" if ok else "FAIL"
            cache_tag = "no-cache" if no_cache else "cached"
            print(f"[fuzz] round {i}/{cfg.runs} ({run_id}, {cache_tag}) -> {status}")
            if not ok:
                failures += 1
                if cfg.on_failure == "stop":
                    print("[fuzz] --on-failure stop; exiting.")
                    return 1
            if _interrupted["campaign"]:
                print(f"[fuzz] campaign aborted by user after round {i}; "
                      f"failures={failures}/{i}")
                return 1

        print(f"[fuzz] done. failures={failures}/{cfg.runs}")
        return 0 if failures == 0 else 2
    finally:
        restore_starting_state(cfg)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
