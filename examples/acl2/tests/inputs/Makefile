TMPFILE = /tmp/workxxx

top: pkg-check.txt

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic
# The following line shouldn't be necessary.
ACL2 ?= acl2

-include Makefile-deps

pkg-check.txt: PKGS.lsp PKGS.sml
	@echo '(include-book "../../lisp/pkg-alist-to-alist")' > $(TMPFILE)
	@echo "(ld (quote (" >> $(TMPFILE)
	@for book in $(BOOKS) ; \
	do \
	echo "(include-book \"$$book\")" >> $(TMPFILE) ; \
	echo '(chk-known-package-alist "PKGS.lsp" state)' >> $(TMPFILE) ; \
	echo '(u)' >> $(TMPFILE) ; \
	done
	@echo "(note-chk-known-package-alist-success \"pkg-check.txt\" state)" >> $(TMPFILE)
	@echo ")))" >> $(TMPFILE)
	@$(ACL2) < $(TMPFILE) > pkg-check.out 2> pkg-check.err
	@if [ ! -e pkg-check.txt ]; then \
	echo "FAILURE for pkg-check.txt" ; \
	exit 1 ; \
	fi

PKGS.lsp PKGS.sml: all
	echo '(include-book "../../lisp/pkg-alist-to-alist")' > $(TMPFILE)
	echo '(include-book "pkg-test")' >> $(TMPFILE)
	echo '(include-book "m1-story")' >> $(TMPFILE)
	echo '(print-kpa "PKGS.lsp" "PKGS.sml")' >> $(TMPFILE)
	$(ACL2) < $(TMPFILE) > PKGS.out 2> PKGS.err

clean: clean-pkgs

clean-pkgs:
	rm -f pkg-check.*
