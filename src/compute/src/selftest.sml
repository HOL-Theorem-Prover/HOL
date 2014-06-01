open HolKernel Parse boolLib testutils

open groundEval

val _ = overload_on ("B1", ``BIT1``);
val _ = overload_on ("B2", ``BIT2``);
val _ = overload_on ("iZ", ``numeral$iZ``);
val _ = overload_on ("NUM", ``NUMERAL``)

val ncset = HOLset.addList(empty_tmset,
                           [``NUMERAL``, ``BIT1``, ``BIT2``,
                            ``0:num``, ``ZERO``]);

val ge0 = GE {constrs = ncset, rwts = Net.empty, case_consts = empty_tmset }
val ge = List.foldl (fn (th,ge) => add_rwt th ge) ge0
                    (Rewrite.mk_rewrites numeralTheory.numeral_distrib @
                     Rewrite.mk_rewrites numeralTheory.numeral_add @
                     Rewrite.mk_rewrites numeralTheory.numeral_suc @
                     Rewrite.mk_rewrites numeralTheory.numeral_iisuc)

fun dot t = reduction ge (vTreeOf ge t) t (Conv (fn x => x));
fun testdot t expected = let
  val result = dot t
in
    aconv (result_term (dot t)) expected andalso
    result_tree result = KnownValue
  orelse
    raise Fail ("Reduction of " ^ term_to_string t ^ " didn't give back " ^
                term_to_string expected)
end;

testdot ``1 + 1`` ``2``;
testdot ``2 + 1`` ``3``;
testdot ``3 + 4`` ``7``;
testdot ``4 + 5 + 9`` ``18``;

testdot ``(\x. x + y) 5`` ``5 + y``;
testdot ``(\x. x + x + 1) ((\y. y + 10) 4)`` ``29``;
