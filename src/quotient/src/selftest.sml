open HolKernel Parse boolLib numLib quotient BasicProvers

val _ = print "Attempting quotient where reln has symbolic name\n"
val _ = temp_remove_termtok {term_name = "<=>", tok = "<=>"}
val _ = hide "<=>"
val eq_def = new_definition("eq_def", ``<=> n m = (n MOD 3 = m MOD 3)``);

val eq_equiv = prove(``!n m. <=> n m = (<=> n = <=> m)``,
                     SRW_TAC [][EQ_IMP_THM, FUN_EQ_THM, eq_def])

val _ = define_quotient_type "mod3" "abs_mod3" "rep_mod3" eq_equiv

open bossLib
val _ = Hol_datatype `foo = C1 | C2`

fun mk_def t = let
  val s = "l" ^ term_to_string t
in
  {def_name = s ^ "_def", fixity = NONE, fname = s, func = t}
end

val thms = define_equivalence_type {
             defs = map mk_def [``C1``, ``C2``],
             equiv = identity_equiv ``:foo``,
             name = "lfoo",
             old_thms = [],
             welldefs = []}

val _ = set_fixity "=" (Infix(NONASSOC, 450))

val thms = define_equivalence_type {
             defs = map mk_def [``C1``, ``C2``],
             equiv = identity_equiv ``:foo``,
             name = "lfoo2",
             old_thms = [],
             welldefs = []}
