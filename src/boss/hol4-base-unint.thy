name: hol-base-unint
version: 1.0
description: HOL basic theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: bool
  import: normal-forms
  import: marker
  import: num
  import: combin
  import: sat
  import: relation
  import: one
  import: pair
  import: prim-rec
  import: arithmetic
  import: sum
  import: poset
  import: numeral
  import: option
  import: basic-size
  import: while
  import: divides
  import: numpair
  import: ind-type
  import: gcd
  import: pred-set
  import: list
  import: rich-list
  import: logroot
  import: set-relation
  import: indexed-lists
  import: bit
  import: numeral-bit
  import: numposrep
  import: quotient
}
bool {
  article: "bool_defs.ot.art"
  interpret: const "HOL4.bool_defs.LET" as "HOL4.bool.LET"
  interpret: const "HOL4.bool_defs.literal_case" as "HOL4.bool.literal_case"
  interpret: const "HOL4.bool_defs.IN" as "HOL4.bool.IN"
  interpret: const "HOL4.bool_defs.TYPE_DEFINITION" as "HOL4.bool.TYPE_DEFINITION"
  interpret: const "HOL4.bool_defs.ARB" as "HOL4.bool.ARB"
}
normal-forms {
  import: bool
  article: "../metis/normalForms.ot.art"
}
marker {
  import: bool
  article: "../marker/marker.ot.art"
}
combin {
  import: bool
  import: marker
  article: "../combin/combin.ot.art"
}
sat {
  import: bool
  article: "../HolSat/sat.ot.art"
}
quotient {
  import: bool
  import: combin
  article: "../quotient/src/quotient.ot.art"
}
relation {
  import: bool
  import: combin
  import: sat
  article: "../relation/relation.ot.art"
}
one {
  import: bool
  article: "../coretypes/one.ot.art"
}
pair {
  import: bool
  import: combin
  import: relation
  import: quotient
  article: "../coretypes/pair.ot.art"
}
poset {
  import: bool
  import: pair
  article: "../coretypes/poset.ot.art"
}
sum {
  import: bool
  import: combin
  import: quotient
  article: "../coretypes/sum.ot.art"
}
option {
  import: bool
  import: combin
  import: relation
  article: "../coretypes/option.ot.art"
}
num {
  import: bool
  article: "../num/theories/num.ot.art"
}
prim-rec {
  import: bool
  import: relation
  import: num
  article: "../num/theories/prim_rec.ot.art"
}
arithmetic {
  import: bool
  import: marker
  import: pair
  import: prim-rec
  import: relation
  article: "../num/theories/arithmetic.ot.art"
}
numeral {
  import: bool
  import: arithmetic
  import: marker
  import: relation
  article: "../num/theories/numeral.ot.art"
}
basic-size {
  import: bool
  import: pair
  import: sum
  import: option
  article: "../num/theories/basicSize.ot.art"
}
while {
  import: bool
  import: combin
  import: relation
  import: arithmetic
  import: sum
  article: "../num/theories/while.ot.art"
}
numpair {
  import: bool
  import: pair
  import: numeral
  import: relation
  import: prim-rec
  import: relation
  article: "../num/extra_theories/numpair.ot.art"
}
divides {
  import: bool
  import: num
  import: arithmetic
  import: numeral
  import: while
  article: "../num/extra_theories/divides.ot.art"
}
logroot {
  import: bool
  import: combin
  import: num
  import: arithmetic
  import: numeral
  import: while
  import: pair
  article: "../num/extra_theories/logroot.ot.art"
}
gcd {
  import: bool
  import: marker
  import: combin
  import: num
  import: arithmetic
  import: numeral
  import: divides
  import: pair
  import: relation
  import: basic-size
  article: "../num/extra_theories/gcd.ot.art"
}
bit {
  import: bool
  import: num
  import: combin
  import: arithmetic
  import: numeral
  import: while
  import: logroot
  article: "../num/extra_theories/bit.ot.art"
}
numeral-bit {
  import: bool
  import: num
  import: combin
  import: arithmetic
  import: numeral
  import: while
  import: pair
  import: logroot
  import: bit
  article: "../num/extra_theories/numeral_bit.ot.art"
}
pred-set {
  import: bool
  import: combin
  import: pair
  import: relation
  import: option
  import: arithmetic
  import: while
  import: prim-rec
  import: normal-forms
  import: numeral
  import: numpair
  import: marker
  import: divides
  article: "../pred_set/src/pred_set.ot.art"
}
set-relation {
  import: bool
  import: marker
  import: pred-set
  import: pair
  import: arithmetic
  import: option
  import: relation
  article: "../pred_set/src/set_relation.ot.art"
}
ind-type {
  import: bool
  import: arithmetic
  import: numpair
  article: "../datatype/ind_type.ot.art"
}
list {
  import: bool
  import: arithmetic
  import: numeral
  import: option
  import: pair
  import: relation
  import: while
  import: marker
  import: pred-set
  import: combin
  import: quotient
  article: "../list/src/list.ot.art"
}
rich-list {
  import: bool
  import: marker
  import: combin
  import: list
  import: arithmetic
  import: pred-set
  import: relation
  import: divides
  article: "../list/src/rich_list.ot.art"
}
indexed-lists {
  import: bool
  import: list
  import: relation
  import: pred-set
  article: "../list/src/indexedLists.ot.art"
}
numposrep {
  import: bool
  import: num
  import: arithmetic
  import: list
  import: bit
  import: numeral
  import: marker
  import: relation
  import: basic-size
  article: "../list/src/numposrep.ot.art"
}
