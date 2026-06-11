#!/usr/bin/env python3
"""Unified live-preview server for the HOL mdbook documentation site.

Serves the built `Manual/book/` tree from a *single origin* -- which is what
cross-book search needs, since `theme/hol-searcher.js` loads each sibling
manual's index via a relative `../<Manual>/searchindex.js` path -- and
live-reloads the browser when a manual's sources change, rebuilding only the
affected manual into `book/<Manual>/`.

Stdlib only (no npm/pip): an `http.server.ThreadingHTTPServer` that injects a
tiny Server-Sent-Events reload client into every HTML page, plus a polling
watcher thread that maps a changed source file to its manual, rebuilds that
manual's book, re-fixes the `searchindex.js -> searchindex-<hash>.js` symlink
(mdbook re-hashes it every build; the recipe, not mdbook, makes the stable
link), and pushes a reload.

This is a *preview* tool: rebuilds run `mdbook build` (and, for Reference,
process_docfiles) directly rather than the full `Holmake mdbook` target, so the
generated sidecars (references.md, labels.tsv, generated SUMMARY.md, ...) and
the `smdpp check-*` gates are not refreshed in the loop.  Run `Holmake mdbook`
before committing.  Run `Holmake mdbook` once first to populate `book/`.
"""

import argparse
import http.server
import os
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path


# --------------------------------------------------------------------------
# Reload broadcast: SSE handlers wait on a generation counter; a rebuild bumps
# it and wakes them.
# --------------------------------------------------------------------------
_cond = threading.Condition()
_generation = 0


def broadcast_reload():
    global _generation
    with _cond:
        _generation += 1
        _cond.notify_all()


# --------------------------------------------------------------------------
# Per-manual rebuild plans.  Each manual maps to the source files to watch and
# the commands that regenerate its book/<name>/ subtree.  Filled in by
# build_manifest() once paths are known.
# --------------------------------------------------------------------------
class Manual:
    def __init__(self, name, src_dir, watch_globs, preprocess=None):
        self.name = name              # also the book/<name>/ subdir
        self.src_dir = src_dir        # cwd for `mdbook build`
        self.watch_globs = watch_globs  # list[Path globs] (callables -> [Path])
        # preprocess(changed, removed): regenerate this manual's mdbook src
        # from the changed source files before rendering.  None for the
        # hand-authored .smd/.md manuals (mdbook reads their dir directly);
        # set for Reference, whose mdbook src is a generated mirror.
        self.preprocess = preprocess
        self.mtimes = None            # last-seen {Path: mtime} of the sources

    def render(self, book_dir):
        """Re-render this book and refresh its searchindex symlink."""
        _run(["mdbook", "build"], cwd=self.src_dir)
        refix_searchindex(book_dir / self.name)


def _log(msg):
    print(f"[livewatch] {msg}", flush=True)


def _run(cmd, cwd):
    """Run a build command, raising CalledProcessError (with output) on failure."""
    subprocess.run(cmd, cwd=cwd, check=True,
                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)


def refix_searchindex(book_manual_dir):
    """Recreate the stable searchindex.js -> searchindex-<hash>.js symlink.

    mdbook hashes the index filename on every build; the cross-book searcher
    loads siblings from a fixed `../<M>/searchindex.js`, so resolve the hash
    here (mirrors each per-manual Holmakefile's mdbook recipe)."""
    hits = sorted(book_manual_dir.glob("searchindex-*.js"))
    if not hits:
        return
    link = book_manual_dir / "searchindex.js"
    if link.is_symlink() or link.exists():
        link.unlink()
    link.symlink_to(hits[0].name)


# Fallback manual list when --manuals isn't passed; the canonical source is
# Manual/mdbook.mk's MANUALS, which the Holmakefile target forwards.
DEFAULT_MANUALS = ["Description", "Tutorial", "Reference",
                   "Interaction-emacs", "Logic", "Developers"]


def build_manifest(repo, book_dir, manual_names):
    """Construct the watch+rebuild plan for the named manuals."""
    manual_root = repo / "Manual"
    theme = manual_root / "theme"

    def dir_globs(d, *patterns):
        return [(lambda d=d, pat=pat: list(d.glob(pat))) for pat in patterns]

    # Reference: mdbook reads a polyscripter-evaluated mirror
    # (build/Docfiles-processed) produced from help/Docfiles/*.smd by
    # process_docfiles.  Rather than rerun the whole ~1580-entry batch on
    # every edit, reprocess only the changed Docfile(s) into the mirror (a
    # fresh process_docfiles session per batch -- correct for the
    # self-contained entries, with the pre-commit `Holmake mdbook` as the
    # source of truth).  render() then re-renders the mirror.
    docfiles = repo / "help" / "Docfiles"
    processed = manual_root / "build" / "Docfiles-processed"
    ref_dir = manual_root / "Reference"
    helpsrc = repo / "help" / "src-sml"
    tools = manual_root / "Tools"

    def reference_preprocess(changed, removed):
        processed.mkdir(parents=True, exist_ok=True)
        # A changed file with no counterpart in the mirror is new; a removal
        # also alters the file set -- either way the sidebar must regenerate.
        fileset_changed = bool(removed) or any(
            not (processed / p.name).exists() for p in changed)
        for p in removed:
            (processed / p.name).unlink(missing_ok=True)
        if changed:
            with tempfile.TemporaryDirectory() as tin, \
                 tempfile.TemporaryDirectory() as tout:
                for p in changed:
                    shutil.copy(p, Path(tin) / p.name)
                _run([str(helpsrc / "process_docfiles"), tin, tout], cwd=helpsrc)
                for f in Path(tout).glob("*.smd"):
                    shutil.copy(f, processed / f.name)
        if fileset_changed:
            with (processed / "SUMMARY.md").open("w") as fh:
                subprocess.run([str(tools / "gen_reference_summary"),
                                str(processed)],
                               check=True, stdout=fh, stderr=subprocess.PIPE,
                               text=True)

    def make_manual(name):
        if name == "Reference":
            return Manual(name, src_dir=ref_dir,
                          watch_globs=dir_globs(docfiles, "*.smd"),
                          preprocess=reference_preprocess)
        # Hand-authored .smd / .md manual: mdbook reads the dir directly, so
        # render() (mdbook build) is the whole rebuild.
        d = manual_root / name
        return Manual(name, src_dir=d,
                      watch_globs=dir_globs(d, "*.smd", "*.md", "book.toml"))

    manuals = [make_manual(n) for n in manual_names]

    # The shared theme/template is baked into every page, so a theme edit
    # rebuilds all manuals.
    theme_watch = dir_globs(theme, "*")
    return manuals, theme_watch


def scan_mtimes(globs):
    """Change fingerprint for a watch group: {path: mtime}."""
    out = {}
    for g in globs:
        for p in g():
            try:
                out[p] = p.stat().st_mtime
            except FileNotFoundError:
                pass
    return out


def watcher(manuals, theme_watch, book_dir, poll, debounce):
    """Poll source mtimes; rebuild changed manual(s) and broadcast reload.

    All manuals track per-file mtimes the same way; the only difference is
    that a manual with a `preprocess` step (Reference) regenerates its mdbook
    source from just the changed files before rendering."""
    for m in manuals:
        m.mtimes = scan_mtimes(m.watch_globs)
    theme_mtimes = scan_mtimes(theme_watch)

    while True:
        time.sleep(poll)
        if scan_mtimes(theme_watch) == theme_mtimes and \
           all(scan_mtimes(m.watch_globs) == m.mtimes for m in manuals):
            continue
        time.sleep(debounce)  # let a burst of saves settle

        theme_now = scan_mtimes(theme_watch)
        theme_changed = theme_now != theme_mtimes
        if theme_changed:
            _log("theme changed -> re-rendering all manuals")
        rebuilt = False
        for m in manuals:
            cur = scan_mtimes(m.watch_globs)
            changed = [p for p, t in cur.items() if m.mtimes.get(p) != t]
            removed = [p for p in m.mtimes if p not in cur]
            if not (changed or removed or theme_changed):
                continue
            t0 = time.monotonic()
            try:
                if m.preprocess and (changed or removed):
                    _log(f"{m.name}: {len(changed)} changed / "
                         f"{len(removed)} removed -> reprocess + render")
                    m.preprocess(changed, removed)
                m.render(book_dir)
            except subprocess.CalledProcessError as e:
                _log(f"{m.name}: BUILD FAILED (keeping last good build)\n"
                     f"{e.output or ''}")
                continue  # leave m.mtimes stale so the next poll retries
            m.mtimes = cur
            _log(f"{m.name}: rebuilt in {time.monotonic() - t0:.1f}s")
            rebuilt = True
        theme_mtimes = theme_now
        if rebuilt:
            broadcast_reload()


# --------------------------------------------------------------------------
# HTTP: static file server over book/, with SSE reload at /__livereload and a
# reload-client snippet injected into every HTML page.
# --------------------------------------------------------------------------
_RELOAD_SNIPPET = (
    b"<script>(function(){try{var e=new EventSource('/__livereload');"
    b"e.onmessage=function(){location.reload();};}catch(_){}}())</script>"
)


def make_handler(book_dir):
    class Handler(http.server.SimpleHTTPRequestHandler):
        def __init__(self, *a, **kw):
            super().__init__(*a, directory=str(book_dir), **kw)

        def log_message(self, *a):
            pass  # quiet; the watcher does the interesting logging

        def do_GET(self):
            if self.path == "/__livereload":
                return self._serve_sse()
            raw = self.path.split("?", 1)[0].split("#", 1)[0]
            target = Path(self.translate_path(self.path))
            if target.is_dir():
                if not raw.endswith("/"):
                    # Let the base class issue its trailing-slash redirect so
                    # the page's relative links resolve against `<dir>/`.
                    return super().do_GET()
                target = target / "index.html"
            # Inject the reload client into HTML; defer everything else (other
            # files, 404s) to the base handler.
            if target.suffix == ".html" and target.is_file():
                return self._serve_html(target)
            return super().do_GET()

        def _serve_html(self, target):
            body = target.read_bytes()
            marker = b"</body>"
            i = body.rfind(marker)
            if i != -1:
                body = body[:i] + _RELOAD_SNIPPET + body[i:]
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-cache")
            self.end_headers()
            try:
                self.wfile.write(body)
            except (BrokenPipeError, ConnectionResetError):
                pass

        def _serve_sse(self):
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream")
            self.send_header("Cache-Control", "no-cache")
            self.send_header("Connection", "keep-alive")
            self.end_headers()
            last = _generation
            try:
                while True:
                    with _cond:
                        fired = _cond.wait_for(
                            lambda: _generation != last, timeout=15)
                        now = _generation
                    if fired:
                        last = now
                        self.wfile.write(b"data: reload\n\n")
                    else:
                        self.wfile.write(b": keepalive\n\n")  # detect drops
                    self.wfile.flush()
            except (BrokenPipeError, ConnectionResetError, ValueError):
                pass  # browser navigated away / reloaded

    return Handler


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve()
    default_repo = here.parents[2]          # <repo>/Manual/Tools/this.py
    ap.add_argument("--repo", type=Path, default=default_repo,
                    help="HOL repo root (default: inferred from script path)")
    ap.add_argument("--book", type=Path, default=None,
                    help="book/ dir to serve (default: <repo>/Manual/book)")
    ap.add_argument("--manuals", default="",
                    help="space-separated manual names to watch; the "
                         "Holmakefile passes mdbook.mk's $(MANUALS) so that "
                         "stays the single source of truth")
    ap.add_argument("--port", type=int, default=3002)
    ap.add_argument("--host", default="0.0.0.0")
    ap.add_argument("--poll", type=float, default=0.5,
                    help="source mtime poll interval, seconds")
    ap.add_argument("--debounce", type=float, default=0.4,
                    help="quiet window after a change before rebuilding")
    args = ap.parse_args()

    repo = args.repo.resolve()
    book_dir = (args.book or repo / "Manual" / "book").resolve()
    if not (book_dir / "index.html").is_file():
        sys.exit(f"{book_dir}/index.html missing -- run `Holmake mdbook` first.")

    names = args.manuals.split() or DEFAULT_MANUALS
    manuals, theme_watch = build_manifest(repo, book_dir, names)

    t = threading.Thread(target=watcher,
                         args=(manuals, theme_watch, book_dir,
                               args.poll, args.debounce),
                         daemon=True)
    t.start()

    httpd = http.server.ThreadingHTTPServer((args.host, args.port),
                                            make_handler(book_dir))
    _log(f"serving {book_dir} at http://{args.host}:{args.port}/ "
         f"(reload on edits to: {', '.join(m.name for m in manuals)}, theme)")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        _log("shutting down")
    finally:
        httpd.shutdown()


if __name__ == "__main__":
    main()
