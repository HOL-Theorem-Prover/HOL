---
title: Authoring HOL Manuals
author: HOL4 Developers
numbersections: yes
---

# Overview

The HOL manuals (Description, Tutorial, ...) are built from a single set of `.smd` source files into two different formats:

  - A PDF via `pandoc` + `latexmk`, for archival / cite-able use.
  - An mdbook HTML site via [`mdbook`](https://rust-lang.github.io/mdBook/), for online browsing.
    Requires **mdbook >= 0.5.0**: the shared page template (`Manual/theme/index.hbs`) is a copy of the mdbook 0.5.x default theme and uses the `{{fa ...}}` FontAwesome helper introduced in 0.5.0.
    `bin/build` checks `mdbook --version` and, on an older (or unreadable) mdbook, warns and falls back to the per-entry HTML reference rather than aborting.

Both formats are driven by the same `.smd` ("scripted markdown") source files, which are an extension of CommonMark.
The extensions are interpreted by the `polyscripter` tool, which runs an embedded Poly/ML session to evaluate HOL fragments inline and splice their pretty-printed output back into the document.

This document is the developer-facing reference for the authoring pipeline.
It is concerned with **how** to write and build a manual; the **content** of each manual is the responsibility of its individual chapters.

# Per-manual file layout

A manual lives in its own subdirectory of `Manual/` (`Manual/Description/`, `Manual/Tutorial/`, ...).
Inside, the moving parts are:

| File                              | Hand-edited?   | Role                                                            |
|-----------------------------------|----------------|-----------------------------------------------------------------|
| `book.toml`                       | yes            | mdbook configuration; **canonical source of the manual title**. |
| `chapters.txt`                    | yes            | canonical chapter ordering (one stem per line).                 |
| `<chapter>.smd`                   | yes            | chapter content.                                                |
| `Holmakefile`                     | yes            | wires the two pipelines together.                               |
| `<manual>.tex`                    | yes            | LaTeX driver: document class, preamble, `\include`s.            |
| `title.tex`, `preface.tex`        | yes            | LaTeX-only front matter (cover + preface).                      |
| `book-title.tex`                  | **generated**  | one-line `\providecommand{\HOLbookTitle}{...}` derived from `book.toml`. |
| `SUMMARY.md`                      | **generated**  | mdbook sidebar; produced from `chapters.txt` by `gen_chap_lists`. |
| `chapters-include.tex`            | **generated**  | LaTeX `\include` block; also from `chapters.txt`.               |
| `<chapter>.md`                    | **generated**  | polyscripter output (`<chapter>.smd` → `.md`).                  |
| `<chapter>.tex`                   | **generated**  | pandoc output (`<chapter>.md` → `.tex`).                        |

All generated files are listed in `.gitignore` and `EXTRA_CLEANS`.

The mdbook page template (`index.hbs`) and stylesheet overrides (`custom.css`) live in `Manual/theme/`, shared by every manual via `theme = "../theme"` in each `book.toml`.
The pandoc Lua filter (`pdf-macros.lua`, e.g. `HOL` → smallcaps) lives in `Manual/Tools/`, referenced from each `Holmakefile` as `../Tools/pdf-macros.lua`.

# Canonical sources of truth

  - **The manual's title** lives in `book.toml`'s `title = "..."`.
    The mdbook menu bar and HTML `<title>` consume it directly.
    The `SUMMARY.md` rule and the `book-title.tex` rule both extract it with a one-line `awk` invocation, so the PDF cover (`title.tex` via `\HOLbookTitle`) and the hyperref `pdftitle` stay automatically in sync.
    Renaming the manual is therefore a single-line edit to `book.toml`.
  - **The chapter ordering** lives in `chapters.txt`.
    Top-level (unindented) lines are chapters; indented lines are nested sub-files of the most recent top-level stem.
    Blank and `#`-comment lines are ignored.
    `gen_chap_lists` reads it twice — once to emit `SUMMARY.md` (the mdbook sidebar) and once to emit `chapters-include.tex` (the LaTeX `\include` block).
  - **The chapter content** lives in `<chapter>.smd`.
    Top-level chapters start with `# Title` (H1), which becomes a `\chapter{}` in the PDF and the page title in mdbook.
    Nested sub-file chapters start with `## Title` (H2) and become `\section{}` in the parent's `\input{<stem>}`.

# The .smd format

An `.smd` file is CommonMark plus polyscripter directives.
The polyscripter reference lives in `Manual/Tools/README`; the high-level summary:

  - Lines starting with `>>` (after stripping leading whitespace!) are HOL inputs.
    Variants: `>>` (run + show I/O), `>>_` (show input, elide output), `>>__` (silent), `>>-` (run, show output only), `>>+` (run; tolerate an unhandled exception).
  - Lines starting with `##xxx` are inline commands: `##thm`, `##eval`, `##assert`, `##parse`, `##use`, `##linelen_limit`, etc.
  - Anything else is plain CommonMark.

Two raw-block flavours let a chapter target one renderer specifically:

```
 ```{=latex}
 ... LaTeX-only content, dropped by smdpp ...
 ```

 ```{=mdbook}
 ... HTML/Markdown-only content, dropped by pandoc ...
 ```
```

Use these for diagrams (e.g. `\begin{picture}` / `\begin{tikzpicture}` for the PDF) and their mdbook equivalents (descriptive prose, `<pre>` blocks, ...).

# Math macros that need to render on both sides

LaTeX `\newcommand`s in the driver `.tex` or in `commands.tex` exist for the PDF only; MathJax in mdbook doesn't see them.
For any math command that appears inside `$...$` or `$$...$$` in chapter prose, **both** sides must declare it:

  - **PDF side:** a `\providecommand{...}` in a `{=latex}` raw block at the top of the chapter.
    YAML `header-includes:` does not survive `pandoc -t latex` and is silently discarded — use the raw block.
  - **mdbook side:** a matching entry in `Manual/theme/index.hbs`'s MathJax `Macros` table.

See `Manual/Tutorial/combin.smd`'s top-of-file block and `Manual/theme/index.hbs`'s `con`/`KC`/`SC`/`mathpredn` entries for a worked example.

# The shared smdpp Poly/ML session

`smdpp` runs **one** Poly/ML session that processes every chapter in `chapters.txt` order.
Anything a chapter does to global state — `load "X"`, overload changes, `Globals.show_X := true`, custom pretty-printers — leaks forward into later chapters.

This is normally what you want (later chapters can rely on earlier `Datatype:` definitions, etc.), but it has two specific gotchas worth highlighting:

  - **Overload leakage.**
    `load "intLib"` in one chapter makes `*`/`+` overloaded for `int` as well as `num` for every later chapter, which can make polymorphic definitions ambiguous and break `metis_tac` searches that were fine in isolation.
    The fix is to bracket the affected chapter with a grammar save/restore against a pristine theory's grammar:

        >>__ val euclid_initial_grammars =
                (Parse.type_grammar(), Parse.term_grammar());
        >>__ Parse.temp_set_grammars $
                valOf $ grammarDB {thyname="numeral"};

        ... chapter body ...

        >>__ Parse.temp_set_grammars euclid_initial_grammars;

    See `Manual/Tutorial/euclid.smd` for a worked example.

  - **Global flag persistence.**
    `set_trace "show_X" 1` or `show_assums := true` similarly stays set for every subsequent `##thm`/`##eval`.
    Always pair the enable with a matching reset at the end of the relevant block.

Both gotchas are *invisible* in the per-chapter pipeline (`Holmake <chapter>.md` starts a fresh polyscripter session per chapter).
**Always rebuild via `Holmake mdbook` before assuming a translated chapter is healthy.**

# Display-only HOL code (`>>` inside non-running blocks)

`polyscripter` strips leading whitespace before checking the directive prefix.
A line `      >> mp_tac (...)` inside a fenced code block intended for display only is still parsed as a `>>` directive and executed against the live goalstack — almost always with a confusing error.

The workaround is to emit the display block as parallel `{=latex}` / `{=mdbook}` raw blocks whose lines begin with `\verb+` (PDF) or `<pre>` + `&gt;&gt;` HTML entities (mdbook), so neither side has `>>` at line start.
See the `EUCLID` box in `Manual/Tutorial/euclid.smd` for the pattern.

# `\cite{}` and bibliography

Both pipelines resolve `\cite{key}` against the manual's `.bib` file, in a Chicago-author-date house style.

  - The author writes `\cite{Foo:2020}` (or `\citep`/`\citet` variants) literally in the `.smd` source.
  - **mdbook side:** the `Holmakefile` runs `smdpp render-bib <manual>.bib ../Tools/csl/chicago-author-date.csl $(SMDS)`, which delegates to `pandoc --citeproc` and produces two sidecar artefacts:
      - `references.md` — the rendered bibliography chapter.
        Hook it into the sidebar by listing `references` as the last entry in `chapters.txt`; `gen_chap_lists latex-include` is hard-wired to skip that stem on the PDF side (natbib handles bibliographies there).
      - `cite-labels.tsv` — preprocessor-time lookup mapping each cite key to its rendered label (e.g. `Foo:2020` → `(Foo 2020)`).
        smdpp's `\cite` pass reads this and rewrites in-prose `\cite{Foo:2020}` to a link into `references.html`.
  - **PDF side:** natbib `[authoryear,round]` plus `\let\cite\citep` in the driver `.tex` renders the bibliography directly from the same `.bib`, sharing the Chicago-author-date style with the mdbook through the CSL the smdpp pass uses.

Per-manual moving parts:

  - `<manual>.bib` — the BibTeX database (hand-edited; the same file feeds both pipelines).
  - `chapters.txt` lists `references` as the last entry so mdbook picks up the bibliography chapter.
  - `Holmakefile`'s `references.md cite-labels.tsv` rule runs `smdpp render-bib`; both outputs are listed in `EXTRA_CLEANS`.
  - The shared CSL lives at `Manual/Tools/csl/chicago-author-date.csl` and is the source of truth for the mdbook citation style.

# Building a single manual

From the manual's directory:

| Target                          | Effect                                                                  |
|---------------------------------|-------------------------------------------------------------------------|
| `Holmake mdbook`                | Generate `SUMMARY.md`, `references.md`, `cite-labels.tsv`, and `labels.tsv`; run `mdbook build`; then `smdpp check-html` + `smdpp check-refs` + `smdpp check-links`. |
| `Holmake <manual>.pdf`          | Generate `chapters-include.tex` + `book-title.tex` + per-chapter `.tex`, then `latexmk` (followed by an explicit trailing `pdflatex` pass for stubborn `.toc` convergence — see any manual's Holmakefile recipe for the rationale). |
| `../Tools/mdbook-preview.py --manual <NAME> [--live]` (run from `Manual/`) | Build this manual via `Holmake mdbook` and serve `Manual/book/<NAME>/` in the foreground. Without `--live`: a plain static server; with `--live`: hand off to `mdbook serve`, which auto-rebuilds + livereloads on edits. Canonical ports: Description 3000, Tutorial 3001, Reference 3003, Interaction-emacs 3004, Logic 3005, Developers 3006 (3002 is the unified site — see below). `--port` overrides. |
| `Holmake <chapter>.md`          | Run polyscripter on one chapter (per-chapter session — does **not** exercise the shared-session gotchas). |
| `Holmake cleanAll`              | Remove all generated files in this dir.                                 |

The two top-level targets (`mdbook` and `<manual>.pdf`) are the gating checks before committing.

# The unified manual site

All manuals are also served as a single mdbook-style site under `Manual/book/`, with a top-level lander, a cross-manual switcher strip above each manual's menu bar, and a unified search index that queries every manual.

## Top-level layout

| Path                              | Role                                                                              |
|-----------------------------------|-----------------------------------------------------------------------------------|
| `Manual/book/index.html`          | Lander: one card per manual, generated by `Manual/Tools/gen_lander` from each `book.toml`. |
| `Manual/book/<Manual>/`           | Per-manual mdbook output (chapters + assets).                                     |
| `Manual/theme/index.hbs`          | Shared Handlebars template — MathJax setup, manual-switcher strip, sidebar JS, `window.HOL_MANUALS.books`. |
| `Manual/theme/custom.css`         | Shared stylesheet.                                                                |
| `Manual/theme/hol-searcher.js`    | Cross-book searcher; replaces mdbook's bundled `searcher.js`.                     |

Each per-manual `book.toml` references the shared theme and the searcher:

    [output.html]
    theme = "../theme"
    additional-css = ["custom.css"]
    additional-js = ["hol-searcher.js"]

`custom.css` and `hol-searcher.js` in each manual's directory are **symlinks** to `../theme/<file>`.
mdbook copies `additional-*` entries by URL-path rather than following filesystem relative paths, so the symlinks keep a single source of truth in `Manual/theme/`.

## Cross-manual references

  - `\ref{Book:label}` — resolves to the URL of `\label{label}` in `Book` (e.g. `../Description/system.html#some-anchor`).
    Each manual's `Holmakefile` runs `../Tools/smdpp dump-labels .` to produce `labels.tsv`, a sidecar that maps every `\label{...}` and heading slug to its rendered URL.
    Every manual's `mdbook` target lists every other manual's `labels.tsv` as a prerequisite, so siblings are built first and resolutions are cross-checked at preprocess time.
  - `\refentry{Foo.bar}` — resolves to the URL of the corresponding Reference entry (`../Reference/Foo.bar.html`).
    `Manual/Reference/entries.list` is the canonical "what entries exist" file; smdpp loads it at startup and dies on an unknown name.

## Cross-manual search

`hol-searcher.js` walks `window.HOL_MANUALS.books` (set in `index.hbs`'s `<head>`), loads each book's `searchindex.js` into its own Elasticlunr index, queries them all on each keystroke, and groups results by book with the current book first.

mdbook hashes the filename of each book's emitted `searchindex.js` (it's content-addressed), so cross-book loads can't reference the hashed name directly.
Each per-manual `Holmakefile`'s `mdbook` target therefore ends with

    cd ../book/<Manual> && \
      ln -sf $$(ls searchindex-*.js | head -1) searchindex.js

to provide a stable, predictable name for the searcher to load.

## Building and serving the unified site

From `Manual/` (not from inside any specific manual's directory):

| Target                          | Effect                                                                              |
|---------------------------------|-------------------------------------------------------------------------------------|
| `Holmake mdbook`                | Build every per-manual book (one recursive `Holmake mdbook` per manual via the `<manual>-mdbook` PHONY targets), then regenerate `Manual/book/index.html` from the four `book.toml`s. |
| `./Tools/mdbook-preview.py [--live]` (run from `Manual/`) | Build the unified site via `Holmake mdbook`, then serve `Manual/book/` at <http://127.0.0.1:3002/> in the foreground. Default is a plain static server; `--live` adds an in-tree watcher + SSE auto-reload — on a source edit only the affected manual is re-rendered via `mdbook build` and the browser reloads. Sidecars (`references.md`, `labels.tsv`, generated `SUMMARY.md`, ...) and the `smdpp check-*` gates are not refreshed mid-loop, so `Holmake mdbook` remains the gating check before committing. |

`Holmake mdbook` from `Manual/` is the gating check before committing changes that touch more than one manual (cross-book `\ref{...}`, theme/template tweaks, etc.); the per-manual `Holmake mdbook` doesn't exercise the cross-book references.

# Adding a new chapter

  1. Write `<stem>.smd`.
     If the chapter is a top-level entry, start with `# Title`; if it is a nested sub-file, start with `## Title`.
  2. Add the stem to `chapters.txt` in the desired position.
     Indent for nested sub-files.
  3. Add per-chapter `<stem>.md` / `<stem>.tex` rules to the Holmakefile, following the existing pattern (most chapters use `$(PS_NOUMAP)` for `.md` and `$(PANDOC_MD)` for `.tex`).
  4. Add `<stem>.md` and `<stem>.tex` to `.gitignore` and the `EXTRA_CLEANS` list.
  5. Run `Holmake mdbook` and `Holmake <manual>.pdf` to verify both pipelines.

# Adding a new manual

  1. `mkdir Manual/<NewManual>` and copy `book.toml` and a minimal `Holmakefile` from `Manual/Tutorial/` as a starting template.  (The mdbook theme is shared from `Manual/theme/`, picked up automatically via the `theme = "../theme"` line in the copied `book.toml`; the `pdf-macros.lua` pandoc filter is shared from `Manual/Tools/` and referenced from the copied `Holmakefile` as `../Tools/pdf-macros.lua`.)
  2. Edit `book.toml`'s `title` and `description` (the description shows up on the lander card emitted by `gen_lander`); set `build-dir = "../book/<NewManual>"`; add an entry for the new manual to the `PORTS` table in `Manual/Tools/mdbook-preview.py` (3000–3006 are taken; 3002 is the unified site).
  3. Symlink the shared theme assets into the manual directory:

         cd Manual/<NewManual>
         ln -s ../theme/custom.css custom.css
         ln -s ../theme/hol-searcher.js hol-searcher.js

  4. Write `<NewManual>.tex` (or `manual.tex`) as the LaTeX driver; both use `\HOLbookTitle` from the auto-generated `book-title.tex`.
  5. Populate `chapters.txt` and add the chapters per the previous section.
  6. Wire the new manual into the unified site:
       - Add `'<NewManual>'` to `window.HOL_MANUALS.books` in `Manual/theme/index.hbs`.
       - Add a `<a data-hol-manual="<NewManual>">` link to the manual-switcher strip in the same template.
       - Add `Manual/<NewManual>/book.toml` to the `book/index.html` recipe's `gen_lander` argument list in `Manual/Holmakefile`.
       - Add `<newmanual>-mdbook` as a `.PHONY` target and a prereq of the aggregate `mdbook` target in `Manual/Holmakefile`.
       - Add `../<NewManual>/labels.tsv` to every sibling manual's `mdbook` target prerequisites so cross-book `\ref{<NewManual>:...}` resolves in either direction.

# Related reference docs

  - `Manual/Tools/README` — exhaustive `polyscripter` directive reference (`>>`/`##xxx` semantics, prompt sizing, expected-failure handling, ...).
  - `Manual/Guide/` — style guidance for writing HOL documentation prose.
  - `Manual/LaTeX/commands.tex` — shared LaTeX macros (`\HOL`, `\ml`, `\holtxt`, `\theoryimp`, ...) available to every manual's PDF build.
  - `Manual/Description/desc-unicode.sty` — `\DeclareUnicodeCharacter` table covering the Unicode codepoints HOL's pretty-printer emits.
    Shared by both Description and Tutorial via `\usepackage{../Description/desc-unicode}`.
