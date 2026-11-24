#!/usr/bin/env python3
"""Stage HOL documentation under the manual lander book/ tree.

Copies per-theory HTML pages and the theory hierarchy graph from their
source-tree locations (where their relative URLs assume the original
layout) into the lander's book/theories/ and book/theory-graph/, and
rewrites cross-file URLs so they resolve correctly from the lander
layout (theories/, theory-graph/, htmlsigs/ are siblings of the
lander's index.html).  htmlsigs/ is owned by makebase (run by
build_help) which writes it directly into book/htmlsigs/.

Usage: stage_references.py HOLDIR BOOK_DIR
"""
import os
import re
import shutil
import sys
from pathlib import Path

if len(sys.argv) != 3:
    sys.exit("Usage: stage_references.py HOLDIR BOOK_DIR")

HOLDIR = Path(sys.argv[1])
BOOK = Path(sys.argv[2])

# A relative `<path>/<thy>Theory.html` -> `<thy>Theory.html`.  Used
# inside theory HTML pages where parent-theory URLs were computed
# relative to the theory's docs directory (`<src>/.hol/docs/`, or
# `<objroot>/docs/<rel>/` under an artifact root); under the lander all
# theory pages are siblings in book/theories/ so the prefix collapses
# away.
THEORY_PARENT_RE = re.compile(
    rb'href="(?![A-Za-z][A-Za-z0-9+.-]*:)[^"]*/([^"/]+?Theory\.html)"'
)

# Same pattern in the theory-graph SVG, but the SVG itself lives at
# book/theory-graph/theories.svg, so theory URLs need to go up one level
# and into book/theories/.  Handles both `href` and `xlink:href`.
SVG_THEORY_RE = re.compile(
    rb'((?:xlink:)?href)="(?![A-Za-z][A-Za-z0-9+.-]*:)[^"]*/'
    rb'([^"/]+?Theory\.html)"'
)


def docs_dir(sig_target, thy_name):
    """The docs directory beside the products directory that sigobj's
    <thy>Theory.sig links into: <src>/.hol/docs for <src>/.hol/objs, or
    <objroot>/docs/<rel> for <objroot>/objs/<rel>.  Prefer one holding
    the theory's page, since a source directory may itself be named
    objs; otherwise the one for the innermost objs."""
    parts = sig_target.parent.parts
    candidates = [Path(*parts[:i], "docs", *parts[i + 1:])
                  for i in reversed(range(len(parts))) if parts[i] == "objs"]
    for d in candidates:
        if (d / f"{thy_name}Theory.html").is_file():
            return d
    return candidates[0] if candidates else None


def canonical_thy_docs():
    """Yield (thy_name, docs_dir) for each theory installed in sigobj/.

    Sigobj is the canonical "production theory" set; walking HOLDIR
    generally would shadow a production theory's page whenever an
    unrelated namesake script exists elsewhere in the tree."""
    sigobj = HOLDIR / "sigobj"
    for entry in sigobj.iterdir():
        name = entry.name
        if not name.endswith("Theory.sig"):
            continue
        thy_name = name[:-len("Theory.sig")]
        if not thy_name or thy_name == "Final" or thy_name.endswith("_emit"):
            continue
        if not entry.is_symlink():
            continue
        docs = docs_dir(Path(os.readlink(entry)), thy_name)
        if docs is not None:
            yield (thy_name, docs)


def stage_theory_pages():
    """Copy Theory.html (rewriting) and Script.html (verbatim) into
    book/theories/.  Earlier symlinks are removed first so the directory
    holds real files we can rewrite in place."""
    target = BOOK / "theories"
    if target.exists():
        # Wipe any prior staging -- the directory may contain stale
        # symlinks left over from an earlier scheme.
        shutil.rmtree(target)
    target.mkdir(parents=True)

    for thy_name, docs in canonical_thy_docs():
        theory_html = docs / f"{thy_name}Theory.html"
        if theory_html.is_file():
            content = theory_html.read_bytes()
            rewritten = THEORY_PARENT_RE.sub(rb'href="\1"', content)
            (target / theory_html.name).write_bytes(rewritten)
        # Script.html pages don't contain cross-theory links worth
        # rewriting; copy as-is.
        script_html = docs / f"{thy_name}Script.html"
        if script_html.is_file():
            shutil.copy2(script_html, target / script_html.name)


def stage_theory_graph():
    """Copy theories.html + theories.svg into book/theory-graph/ and
    rewrite node URLs so they target ../theories/<thy>Theory.html."""
    src_dir = HOLDIR / "help" / "theorygraph"
    svg = src_dir / "theories.svg"
    html = src_dir / "theories.html"
    if not svg.is_file() or not html.is_file():
        # `dot` wasn't installed at build time; nothing to stage.
        return

    target = BOOK / "theory-graph"
    # An earlier scheme symlinked this directory; replace cleanly so
    # the staged files are real (rewritable) copies.
    if target.is_symlink():
        target.unlink()
    elif target.exists():
        shutil.rmtree(target)
    target.mkdir(parents=True)

    shutil.copy2(html, target / "theories.html")
    svg_bytes = svg.read_bytes()
    rewritten = SVG_THEORY_RE.sub(
        rb'\1="../theories/\2"', svg_bytes
    )
    (target / "theories.svg").write_bytes(rewritten)


# References to <thy>Theory.html (or <thy>Script.html) found in the
# staged content.  Used to discover which theories are pointed at but
# have no per-theory HTML in the build state.
LINK_RE = re.compile(rb'href="([A-Za-z0-9_]+(?:Theory|Script)\.html)"')
SVG_LINK_RE = re.compile(
    rb'(?:xlink:)?href="\.\./theories/([A-Za-z0-9_]+(?:Theory|Script)\.html)"'
)

STUB_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>{name}</title>
<style>
  body {{ font-family: system-ui, sans-serif; max-width: 640px;
         margin: 4em auto; padding: 0 1em; color: #222; line-height: 1.5; }}
  code {{ font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }}
  a {{ color: #4183c4; }}
</style>
</head>
<body>
<h1><code>{name}</code></h1>
<p>No per-theory documentation page was generated for
<code>{name}</code> during the last build.  Theory bindings for this
theory are still listed in the
<a href="../htmlsigs/TheoryIndex.html">theory bindings index</a>.</p>
<p><a href="../index.html">Back to the HOL4 documentation landing page</a>.</p>
</body>
</html>
"""


def stub_missing_theories():
    """For every Theory.html or Script.html referenced by staged content
    that has no real file in book/theories/, drop in a stub page so the
    link doesn't 404."""
    theories_dir = BOOK / "theories"
    present = {p.name for p in theories_dir.glob("*.html")}

    referenced = set()
    for path in theories_dir.glob("*Theory.html"):
        for m in LINK_RE.finditer(path.read_bytes()):
            referenced.add(m.group(1).decode())

    svg = BOOK / "theory-graph" / "theories.svg"
    if svg.is_file():
        for m in SVG_LINK_RE.finditer(svg.read_bytes()):
            referenced.add(m.group(1).decode())

    missing = referenced - present
    for name in sorted(missing):
        # name ends in either Theory.html or Script.html; strip suffix for
        # the display heading.
        base = name[:-len(".html")]
        (theories_dir / name).write_text(
            STUB_TEMPLATE.format(name=base)
        )


def main():
    stage_theory_pages()
    stage_theory_graph()
    stub_missing_theories()


if __name__ == "__main__":
    main()
