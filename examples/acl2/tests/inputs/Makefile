CERTS := $(patsubst %.lisp, %.cert, $(wildcard *.lisp))

.PHONY: top
top: $(CERTS)

include ${ACL2_SYSTEM_BOOKS}/Makefile-generic
# The following line shouldn't be necessary.
ACL2 ?= acl2

# From make dependencies:

apply-total-order.cert: apply-total-order.lisp
apply-total-order.cert: total-order.cert

circuit-bisim.cert: circuit-bisim.lisp
circuit-bisim.cert: ltl.cert

circuits.cert: circuits.lisp
circuits.cert: circuit-bisim.cert

cone-of-influence.cert: cone-of-influence.lisp
cone-of-influence.cert: circuits.cert
# cone-of-influence.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-2/meta/top.cert

encap1.cert: encap1.lisp

ltl.cert: ltl.lisp
ltl.cert: sets.cert

records.cert: records.lisp
records.cert: apply-total-order.cert

sets.cert: sets.lisp
sets.cert: records.cert

summary.cert: summary.lisp
summary.cert: cone-of-influence.cert
summary.cert: records.cert
summary.cert: cone-of-influence.cert

test1.cert: test1.lisp

test1a.cert: test1a.lisp

test2.cert: test2.lisp

total-order.cert: total-order.lisp
