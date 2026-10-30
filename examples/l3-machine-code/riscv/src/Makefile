# Regenerate the HOL4 theory and the SML emulator from riscv.spec with L3.
#
# Needs L3 (L3-2018-02-09 from https://acjf3.github.io/l3/, built with
# Poly/ML) with `l3` on PATH, or `make L3=/path/to/L3-2018-02-09/bin/l3`.
# Each export takes a few seconds.
#
#   make          regenerate ../model/{riscvScript.sml,riscvLib.sml,riscvLib.sig,
#                 riscv.sml,riscv.sig}
#   make check    regenerate into a temporary directory and compare with ../model
#                 (ignoring the timestamp in the first line); exit 1 on a difference
#
# Two things are patched into L3's output so that `make check` is clean on an
# unchanged spec: a trailing newline at end of file, and `temp_prefer_num` in
# riscvLib.sml (HOL commit 0a75ce84c). The SML export uses `nointinf`, matching
# the committed riscv.sml.

SHELL    := /bin/bash
L3       ?= l3
SPEC      = riscv.spec
HOLFILES  = riscvScript.sml riscvLib.sml riscvLib.sig
SMLFILES  = riscv.sml riscv.sig
MODEL     = ../model

HOLEXPORT = echo 'HolExport.spec ("$(SPEC)", "riscv")' | $(L3)
SMLEXPORT = echo 'SMLExport.spec ("$(SPEC)", "riscv nointinf")' | $(L3)
PATCHHOL  = sed -i -e 's/numLib\.prefer_num ()/numLib.temp_prefer_num ()/' -e '$$a\' $(HOLFILES)
PATCHSML  = sed -i -e '$$a\' $(SMLFILES)

all: hol sml
.PHONY: all hol sml check

hol: $(SPEC)
	$(HOLEXPORT)
	$(PATCHHOL)
	mv $(HOLFILES) $(MODEL)/

sml: $(SPEC)
	$(SMLEXPORT)
	$(PATCHSML)
	mv $(SMLFILES) $(MODEL)/

check: $(SPEC)
	@tmp=$$(mktemp -d) && cp $(SPEC) $$tmp && cd $$tmp && \
	$(HOLEXPORT) > hol.log 2>&1 && $(SMLEXPORT) > sml.log 2>&1 && \
	$(PATCHHOL) && $(PATCHSML) && status=0 && \
	for f in $(HOLFILES) $(SMLFILES); do \
	  if diff <(tail -n +2 $$f) <(tail -n +2 $(CURDIR)/$(MODEL)/$$f) > /dev/null; \
	  then echo "$$f: identical"; else echo "$$f: DIFFERS from $(MODEL)/$$f"; status=1; fi; \
	done; \
	rm -rf $$tmp; exit $$status
