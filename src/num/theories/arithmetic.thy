name: arithmetic
version: 1.0
description: HOL4 arithmetic
author: HOL4 people
license: BSD
show: "HOL4"
show: "Data.Bool"
show: "Number.Natural"
show: "Relation"
requires: base
main {
  import: combin
  article: "strippedarith.art"
  interpret: const "HOL4.bool.!" as "Data.Bool.!"
  interpret: const "HOL4.bool.?" as "Data.Bool.?"
  interpret: const "HOL4.bool.T" as "Data.Bool.T"
  interpret: const "HOL4.bool.F" as "Data.Bool.F"
  interpret: const "HOL4.bool./\\" as "Data.Bool./\\"
  interpret: const "HOL4.bool.\\/" as "Data.Bool.\\/"
  interpret: const "HOL4.min.==>" as "Data.Bool.==>"
  interpret: const "HOL4.bool.~" as "Data.Bool.~"
  interpret: const "HOL4.bool.COND" as "Data.Bool.cond"
  interpret: const "HOL4.bool.LET" as "Data.Bool.let"
  interpret: const "HOL4.bool.ONE_ONE" as "Function.injective"
  interpret: const "HOL4.bool.ARB" as "Data.Bool.arb"

  interpret: type "HOL4.num.num" as "Number.Natural.natural"
  interpret: const "HOL4.num.0" as "Number.Natural.zero"
  interpret: const "HOL4.num.SUC" as "Number.Natural.suc"
  interpret: const "HOL4.prim_rec.<" as "Number.Natural.<"
  interpret: const "HOL4.relation.TC" as "Relation.transitiveClosure"
  interpret: const "HOL4.combin.o" as "Function.o"
  interpret: const "HOL4.combin.K" as "Function.const"
  interpret: const "HOL4.combin.S" as "Combinator.s"
}
combin {
  interpret: const "HOL4.bool.ARB" as "Data.Bool.arb"
  interpret: const "HOL4.bool.ONE_ONE" as "Function.injective"
  interpret: const "HOL4.bool.COND" as "Data.Bool.cond"
  interpret: const "HOL4.bool.LET" as "Data.Bool.let"
  interpret: const "HOL4.bool.~" as "Data.Bool.~"
  interpret: const "HOL4.bool.\\/" as "Data.Bool.\\/"
  interpret: const "HOL4.bool.!" as "Data.Bool.!"
  interpret: const "HOL4.bool.?" as "Data.Bool.?"
  interpret: const "HOL4.bool.T" as "Data.Bool.T"
  interpret: const "HOL4.bool.F" as "Data.Bool.F"
  interpret: const "HOL4.bool./\\" as "Data.Bool./\\"
  interpret: const "HOL4.min.==>" as "Data.Bool.==>"

  interpret: const "HOL4.relation.TC" as "Relation.transitiveClosure"
  interpret: const "HOL4.combin.o" as "Function.o"
  interpret: const "HOL4.combin.K" as "Function.const"
  interpret: const "HOL4.combin.S" as "Combinator.s"
  article: "../../combin/combin.ot.art"
}
