# Shared definitions for the unified mdbook site.  Each per-manual
# Holmakefile sets THIS to its own stem and then `include's this
# file; Manual/Holmakefile `include's it too for the aggregator's
# per-book MDBOOK_TARGETS / BOOK_TOMLS lists.  Adding a new manual
# is a one-line edit to MANUALS here.

MANUALS = Description Tutorial Reference Interaction-emacs

# All sibling manuals' labels.tsv files, relative to the including
# manual's directory: the first $(patsubst) drops the self-entry,
# the second prefixes ../<M>/labels.tsv.
SIBLING_LABELS = $(patsubst %,../%/labels.tsv,$(patsubst $(THIS),,$(MANUALS)))
