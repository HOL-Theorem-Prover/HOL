#!/usr/bin/env python3
"""Local preview server for the HOL mdbook documentation site.

Wraps `Holmake mdbook` (unified) or per-manual `Holmake mdbook` with a
foreground HTTP server so the freshly-built site can be browsed locally.
This replaces the old `Holmake mdbook-serve` / `mdbook-livewatch` /
per-manual `mdbook-serve` recipes: long-running server processes are
started from a script rather than from Holmake.

Default: rebuild and serve the unified site statically on port 3002.

    ./Tools/mdbook-preview.py                   # unified, static
    ./Tools/mdbook-preview.py --live            # unified, watch+reload
    ./Tools/mdbook-preview.py --manual Tutorial # one manual, static
    ./Tools/mdbook-preview.py --manual Logic --live   # one manual, live

`--live` for the unified site uses an in-tree watcher + SSE auto-reload:
on source edits, only the affected manual is re-rendered via
`mdbook build` and the browser reloads.  Sidecars (references.md,
labels.tsv, generated SUMMARY.md, ...) and the `smdpp check-*` gates
are NOT refreshed mid-loop -- the pre-serve `Holmake mdbook` covers
them, and a fresh `Holmake mdbook` is still the gating check before
committing.

`--live` for a single manual delegates to mdbook's own `mdbook serve`,
which provides livereload + auto-rebuild for that manual on its own.

Stdlib only.  Requires `mdbook` on PATH for `--manual N --live`.
"""

import argparse
import http.server
import shutil
import socket
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path


# Canonical port per manual; `--port` overrides.  Distinct values so
# any combination of these servers can run side by side.
PORTS = {
    None:                3002,  # unified site
    "Description":       3000,
    "Tutorial":          3001,
    "Reference":         3003,
    "Interaction-emacs": 3004,
    "Logic":             3005,
    "Developers":        3006,
}


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
    print(f"[mdbook-preview] {msg}", flush=True)


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


def read_manuals_mk(repo):
    """Return the MANUALS list declared in Manual/mdbook.mk."""
    path = repo / "Manual" / "mdbook.mk"
    for raw in path.read_text().splitlines():
        tokens = raw.split("#", 1)[0].split()
        if tokens[:2] == ["MANUALS", "="]:
            return tokens[2:]
    sys.exit(f"Couldn't find MANUALS in {path}")


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
# HTTP: static file server over book/, with optional SSE livereload (gated
# by the `live` flag) injecting a reload client into every HTML page.
# --------------------------------------------------------------------------
_RELOAD_SNIPPET = (
    b"<script>(function(){try{var e=new EventSource('/__livereload');"
    b"e.onmessage=function(){location.reload();};}catch(_){}}())</script>"
)


def make_handler(book_dir, live):
    class Handler(http.server.SimpleHTTPRequestHandler):
        def __init__(self, *a, **kw):
            super().__init__(*a, directory=str(book_dir), **kw)

        def log_message(self, *a):
            pass  # quiet; the watcher does the interesting logging

        def do_GET(self):
            if not live:
                return super().do_GET()
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


def check_port_free(host, port):
    """Fail fast on port collision (before the slow Holmake step)."""
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    try:
        s.bind((host, port))
    except OSError:
        sys.exit(
            f"Port {port} already in use; stop the existing server first.")
    finally:
        s.close()


def ensure_built(repo, manual):
    """Run `Holmake mdbook` so the served site matches a release build."""
    cwd = repo / "Manual" / manual if manual else repo / "Manual"
    label = f"Manual/{manual}" if manual else "Manual"
    _log(f"building {label} via Holmake mdbook ...")
    try:
        subprocess.run(["Holmake", "mdbook"], cwd=cwd, check=True)
    except FileNotFoundError:
        sys.exit("Holmake not on PATH; add <repo>/bin to your shell's "
                 "PATH and retry.")
    except subprocess.CalledProcessError as e:
        sys.exit(f"Holmake mdbook in {cwd} failed (exit {e.returncode}); "
                 f"server not started.")


def _serve_forever(httpd):
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        _log("shutting down")
    finally:
        httpd.shutdown()


def _display_host(host):
    """A browser-connectable host for the printed URL.  We bind 0.0.0.0
    (::) so the server is reachable on every interface, but those are
    wildcard bind addresses, not destinations -- a browser wants
    localhost.  Map them; leave an explicitly-given host alone."""
    return "localhost" if host in ("0.0.0.0", "::") else host


def serve(book_dir, host, port, live=False):
    """Foreground HTTP server over book_dir.  Caller starts any watcher."""
    if not (book_dir / "index.html").is_file():
        sys.exit(f"{book_dir}/index.html missing after Holmake mdbook -- "
                 f"unexpected; aborting.")
    httpd = http.server.ThreadingHTTPServer((host, port),
                                            make_handler(book_dir, live))
    mode = "live (watch + reload)" if live else "static"
    _log(f"serving {book_dir} at http://{_display_host(host)}:{port}/  "
         f"[{mode}]")
    _serve_forever(httpd)


def mdbook_serve(src_dir, host, port):
    """Hand off to mdbook's own livereload server: it watches the manual's
    sources and rebuilds + reloads automatically."""
    _log(f"running mdbook serve in {src_dir} at "
         f"http://{_display_host(host)}:{port}/  [live]")
    try:
        subprocess.run(
            ["mdbook", "serve", "--hostname", host, "--port", str(port)],
            cwd=src_dir, check=False)
    except KeyboardInterrupt:
        pass


def start_unified_watcher(repo, book_dir, poll, debounce):
    manuals, theme_watch = build_manifest(repo, book_dir,
                                          read_manuals_mk(repo))
    threading.Thread(target=watcher,
                     args=(manuals, theme_watch, book_dir, poll, debounce),
                     daemon=True).start()


def main():
    ap = argparse.ArgumentParser(
        description="Local preview server for the HOL mdbook site.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__)
    here = Path(__file__).resolve()
    default_repo = here.parents[2]          # <repo>/Manual/Tools/this.py
    ap.add_argument("--repo", type=Path, default=default_repo,
                    help="HOL repo root (default: inferred from script path)")
    ap.add_argument("--manual", default=None,
                    choices=[m for m in PORTS if m is not None],
                    help="serve just this manual (default: unified site)")
    ap.add_argument("--live", action="store_true",
                    help="enable livereload (unified: in-tree watcher + SSE; "
                         "per-manual: mdbook's own livereload server)")
    ap.add_argument("--port", type=int, default=None,
                    help="override the canonical port for this scope")
    ap.add_argument("--host", default="0.0.0.0")
    ap.add_argument("--poll", type=float, default=0.5,
                    help="(unified --live) source mtime poll interval, sec")
    ap.add_argument("--debounce", type=float, default=0.4,
                    help="(unified --live) quiet window after a change, sec")
    args = ap.parse_args()

    repo = args.repo.resolve()
    port = args.port if args.port is not None else PORTS[args.manual]
    manual_root = repo / "Manual"

    check_port_free(args.host, port)
    ensure_built(repo, args.manual)

    if args.manual is None:
        book_dir = (manual_root / "book").resolve()
        if args.live:
            start_unified_watcher(repo, book_dir, args.poll, args.debounce)
        serve(book_dir, args.host, port, live=args.live)
    elif args.live:
        mdbook_serve(manual_root / args.manual, args.host, port)
    else:
        serve((manual_root / "book" / args.manual).resolve(), args.host, port)


if __name__ == "__main__":
    main()
