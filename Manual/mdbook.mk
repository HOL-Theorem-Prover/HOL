# Shared definitions for the unified mdbook site.  Each per-manual
# Holmakefile sets THIS to its own stem and then `include's this
# file; Manual/Holmakefile `include's it too for the aggregator's
# per-book MDBOOK_TARGETS / BOOK_TOMLS lists.  Adding a new manual
# is a one-line edit to MANUALS here.

MANUALS = Description Tutorial Quick Reference Interaction-emacs Logic Developers

# All sibling manuals' labels.tsv files, relative to the including
# manual's directory: the first $(patsubst) drops the self-entry,
# the second prefixes ../<M>/labels.tsv.
SIBLING_LABELS = $(patsubst %,../%/labels.tsv,$(patsubst $(THIS),,$(MANUALS)))

# The shared mdbook theme/template files (index.hbs is baked into
# every rendered page; custom.css / hol-searcher.js are pulled in via
# each book.toml).  `mdbook build` itself always rebuilds the whole
# book, so the Holmake mtime gate on ../book/<THIS>/index.html is the
# only incremental layer -- without these as prerequisites a theme
# edit leaves every book stale.  $(wildcard) keeps the (flat) theme
# directory's contents in sync automatically.
THEME_DEPS = $(wildcard ../theme/*)

# Attach the theme files (and book.toml) to this manual's book
# target.  Recipe-less rule (the real recipe lives in the per-manual
# Holmakefile); guarded on THIS so the aggregator's include of this
# file -- which leaves THIS unset -- doesn't synthesise a bogus
# ../book//index.html node.  A theme change therefore invalidates
# every manual's book, which is correct: they all bake the same
# template in.  book.toml is included directly so its title /
# preprocessor / mathjax settings are tracked even where SUMMARY.md
# is hand-written (Developers) rather than generated from book.toml.
ifdef THIS
../book/$(THIS)/index.html: $(THEME_DEPS) book.toml
endif
