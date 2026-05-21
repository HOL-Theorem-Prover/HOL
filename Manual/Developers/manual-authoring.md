---
title: Authoring HOL Manuals
author: HOL4 Developers
numbersections: yes
---

# Overview

The HOL manuals (Description, Tutorial, ...) are built from a single set of `.smd` source files into two different formats:

  - A PDF via `pandoc` + `latexmk`, for archival / cite-able use.
  - An mdbook HTML site via [`mdbook`](https://rust-lang.github.io/mdBook/), for online browsing.

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

Citations are not yet wired into the mdbook pipeline.
The current convention is:

  - Leave `\cite{key}` calls as raw LaTeX in the `.smd`.
    Pandoc resolves them for the PDF against the manual's `references.tex` / `.bib`.
  - mdbook renders them literally as `\cite{key}`.

This is tracked as a follow-up; do not introduce ad-hoc workarounds.

# Building

From the manual's directory:

| Target                          | Effect                                                                  |
|---------------------------------|-------------------------------------------------------------------------|
| `Holmake mdbook`                | Generate `SUMMARY.md`, run `mdbook build`, then `mdbook-check.sh` + `smdpp check-refs`. |
| `Holmake <manual>.pdf`          | Generate `chapters-include.tex` + `book-title.tex` + per-chapter `.tex`, then `latexmk`. |
| `Holmake mdbook-serve`          | Background `mdbook serve`. Each manual uses a different port (Description:3000, Tutorial:3001). |
| `Holmake <chapter>.md`          | Run polyscripter on one chapter (per-chapter session — does **not** exercise the shared-session gotchas). |
| `Holmake cleanAll`              | Remove all generated files in this dir.                                 |

The two top-level targets (`mdbook` and `<manual>.pdf`) are the gating checks before committing.

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
  2. Edit `book.toml`'s `title` to the new manual's name; pick a distinct port for `mdbook-serve`; set `build-dir = "../book/<NewManual>"`.
  3. Write `<NewManual>.tex` (LaTeX driver) and `title.tex` (PDF cover); both use `\HOLbookTitle` from the auto-generated `book-title.tex`.
  4. Populate `chapters.txt` and add the chapters per the previous section.

# Related reference docs

  - `Manual/Tools/README` — exhaustive `polyscripter` directive reference (`>>`/`##xxx` semantics, prompt sizing, expected-failure handling, ...).
  - `Manual/Guide/` — style guidance for writing HOL documentation prose.
  - `Manual/LaTeX/commands.tex` — shared LaTeX macros (`\HOL`, `\ml`, `\holtxt`, `\theoryimp`, ...) available to every manual's PDF build.
  - `Manual/Description/desc-unicode.sty` — `\DeclareUnicodeCharacter` table covering the Unicode codepoints HOL's pretty-printer emits.
    Shared by both Description and Tutorial via `\usepackage{../Description/desc-unicode}`.
