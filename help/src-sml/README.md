# `help/src-sml`

Tools that build HOL's help facilities from the per-entry sources in
`help/Docfiles/*.smd`.  Driven from `bin/build`'s
[`build_help`](../../tools/build/buildutils.sml) step.

## What gets produced

For each entry under `help/Docfiles/` (one `.smd` per HOL identifier),
the pipeline produces:

  - `help/Docfiles/<entry>.txt`
    — plain-text rendering used by the in-HOL `help "<entry>"`
    command.  Built by [`process_docfiles`](process_docfiles.sml).

  - `Manual/build/Docfiles-processed/<entry>.smd`
    — the same source but with every polyscripter `>>` directive
    evaluated against a live HOL session.  Consumed downstream by
    both the mdbook Reference manual and `Md2TeX` (for
    `reference.pdf`); see [polyscripter](../../Manual/Tools/polyscripter.sml).

  - `help/Docfiles/HTML/<entry>.html` *(fallback only)*
    — per-entry standalone HTML pages, produced when `mdbook` is
    absent from PATH or `bin/build --no-mdbook` is passed.  When
    `mdbook` is present the Reference book at
    `Manual/book/Reference/<entry>.html` takes the place of these.

In parallel, `makebase.exe` reads the `.txt` files and:

  - builds the binary database (`help/HOL.Help`) that the in-HOL
    `help` command queries;
  - renders the `.sig` files in `sigobj/` to
    `help/src-sml/htmlsigs/<struct>.html` (one per loaded
    structure), with each identifier hyperlinking into either the
    mdbook entry or the fallback HTML;
  - writes `help/HOL.LanderFragment.html`, the embeddable card list
    of libraries / theories / syntax modules / simpsets that
    `Manual/Tools/gen_lander` slots into the unified
    `Manual/book/index.html` landing page.

## Build flow

```
help/Docfiles/<entry>.smd
        │
        ▼  process_docfiles (single buildheap binary, one polyscripter
        │   pass over every entry; one pandoc invocation per output
        │   format with sentinel-based split)
        │
        ├──────────────────────────────────┐
        ▼                                  ▼
Manual/build/Docfiles-processed/   help/Docfiles/<entry>.txt
   <entry>.smd                              │
        │                                   │
        ├────────────────┬─────────────┐    │
        ▼                ▼             ▼    ▼
   mdbook /          Md2TeX →     (sig→html: Htmlsigs reads these
   smdpp             entries.tex          and writes htmlsigs/)
   (Reference)       → reference.pdf      │
        │                                 │
        ▼                                 ▼
   Manual/book/                     help/src-sml/htmlsigs/
     Reference/                       <struct>.html
```

A single buildheap binary (`process_docfiles`) loads `bin/hol.state`
once, evaluates every entry's `>>` directives sharing one Poly/ML
compiler session, then runs `pandoc` once per output format
(`-t plain` for `.txt`, optionally `-t html` for the fallback pages)
on the concatenation of processed entries with sentinels between
them, and splits the result back into per-entry files.

## CLI flags surfaced by `bin/build`

  - `--no-mdbook` — skip the Reference mdbook step even if
    `mdbook` is on PATH; produce per-entry HTML via the pandoc
    fallback instead.
  - `--no-helpdocs` — skip the entire help-documentation build
    (no docfile processing, no mdbook, no help DB).  Useful for
    partial sequences (e.g. `bin/build --seq=tools/sequences/upto-parallel`)
    that haven't compiled every HOL library and so can't
    successfully evaluate every `>>` directive.

## Adding documentation

Drop a new `<structure>.<id>.smd` (or `<structure>.smd`) into
`help/Docfiles/`.  Symbolic identifiers are encoded via
`UC_ASCII_Encode.encode` (call it from a HOL session) and the
encoded name is separated from the structure name by **two** dots:
`<structure>..<encoded-name>.smd`.

`.smd` files are CommonMark with polyscripter extensions: lines
prefixed `>>` are evaluated as ML and replaced by an interactive
transcript, `>>__` is silent setup, `>>+` continues a prior block,
etc.; full reference in
[`Manual/Tools/polyscripter.sml`](../../Manual/Tools/polyscripter.sml).
A typical entry opens with

```
>>__ load "wordsLib"; Parse.temp_set_grammars $ valOf $ grammarDB {thyname="words"};
```

to pin the parser grammar to whatever theory the entry's
`>>` examples need.

### Aliasing

When the same identifier is exported from several structures
(e.g. `bossLib.Cases_on` re-exports `BasicProvers.Cases_on`), one
`.smd` is designated the canonical home for the prose.  It carries
YAML frontmatter listing every alias:

```
---
aliases:
  - BasicProvers.Cases_on
---
```

Alias entries themselves are tiny stubs that point back at the
canonical and are marked auto-generated:

```
---
canonical: bossLib.Cases_on
generated: true
---
```

Stub bodies and the canonical's "Also exported as" line (between
`<!-- BEGIN aliases-block -->` and `<!-- END aliases-block -->` HTML
markers) are maintained by `AliasGen.exe`:

```
AliasGen.exe --check ../Docfiles    # CI: verify all aliases consistent
AliasGen.exe --regen ../Docfiles    # rewrite stubs from canonicals
```

`build_help` runs `--check` as part of every `bin/build`; the build
fails if alias entries are out of sync.

## Provenance

`makebase`, `Htmlsigs`, the underlying `Database` / `Asynt` /
`ParseDoc` machinery, and the directory layout descend from Peter
Sestoft's original Moscow ML helpsigs code
(`mosml/src/doc/helpsigs/`, 1996–2000).
