CERTS := $(patsubst %.lisp, %.cert, $(wildcard *.lisp))

.PHONY: top
top: $(CERTS)

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic
# The following line shouldn't be necessary.
ACL2 ?= acl2

-include Makefile-deps
