(*
quietdec := true;

val home_dir = (concat Globals.HOLDIR "/examples/temporal_deep/");
loadPath := (concat home_dir "src/deep_embeddings") ::
            (concat home_dir "src/tools") :: !loadPath;

map load
 ["congLib", "temporal_deep_simplificationsLib",
  "prop_logicTheory", "full_ltlTheory", "Travrules", "simpLib", "Trace"];
*)

open HolKernel boolLib bossLib temporal_deep_simplificationsLib
  congLib prop_logicTheory full_ltlTheory Travrules simpLib Trace

(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)








(*

trace_level := 0
(*Trace level 0 .. 5*)


val prop1 = ``P_AND(P_NOT(P_NOT y), x)``
val prop2 = ``P_AND(P_PROP (3+1), P_PROP(2+2))``
val prop3 = ``P_AND(P_AND(a, b), a)``

val prop4 = ``P_AND(P_OR(b, b), a)``

val prop5 = ``PROP_LOGIC_EQUIVALENT (P_AND(b, b)) (P_AND(P_OR(b, c), a))``


(*Some simple rewrite*)
CONGRUENCE_SIMP_CONV ``PROP_LOGIC_EQUIVALENT`` prop_logic_cs std_ss [] prop1;

(*Also works for equality, but does of course not simplify als much*)
CONGRUENCE_EQ_SIMP_CONV prop_logic_cs std_ss [] prop2;

(*Here equality may be more useful*)
CONGRUENCE_EQ_SIMP_CONV prop_logic_cs std_ss [] prop5;


(*There are also tactics*)

val thm = prove (``!x y. PROP_LOGIC_EQUIVALENT (P_OR(x, P_AND(y, y))) (P_OR(x, y))``,
CONGRUENCE_SIMP_TAC prop_logic_cs std_ss []);


val thm = prove (``!x y z. PROP_LOGIC_EQUIVALENT y z ==> PROP_LOGIC_EQUIVALENT (P_OR(x, P_AND(y, z))) (P_OR(x, y))``,

CONGRUENCE_SIMP_TAC prop_logic_cs std_ss []);

val thm = prove (``!x y z. PROP_LOGIC_EQUIVALENT y z ==> PROP_LOGIC_EQUIVALENT (P_OR(x, P_AND(y, z))) (P_OR(x, y))``,

REPEAT STRIP_TAC THEN
ASM_CONGRUENCE_SIMP_TAC prop_logic_cs std_ss []);


val thm = prove (``!x y z. PROP_LOGIC_EQUIVALENT (P_AND(y, y)) z ==> PROP_LOGIC_EQUIVALENT (P_OR(x, P_AND(y, z))) (P_OR(x, y))``,

REPEAT STRIP_TAC THEN
FULL_CONGRUENCE_SIMP_TAC prop_logic_cs std_ss []);




(*There are also rules*)
val thm = CONGRUENCE_EQ_SIMP_CONV prop_logic_dnf_cs std_ss [] prop4;
CONGRUENCE_SIMP_RULE prop_logic_dnf_cs std_ss [] thm;


(*with a empty_congset it behaves like a SIMP_CONV*)
CONGRUENCE_EQ_SIMP_CONV empty_congset std_ss [P_OR_def] prop4;



(*Some LTL examples*)
val ltl1 = ``LTL_AND(LTL_NOT(LTL_NOT y), x)``;
val ltl2 = ``LTL_AND(x, y)``;
val ltl3 = ``LTL_AND(LTL_NOT(LTL_NOT(LTL_AND(x, LTL_NOT(LTL_NOT y)))), x)``;
val ltl4 = ``LTL_AND(LTL_NOT(LTL_SWHILE(LTL_AND (LTL_PROP b, LTL_PROP (P_OR(b, P_FALSE))), LTL_NOT(LTL_NOT y))), x)``;
val ltl5 = ``LTL_OR(LTL_AND(LTL_ALWAYS a, LTL_ALWAYS b), c)``;
val ltl6 = ``LTL_NOT(LTL_OR(LTL_AND(LTL_ALWAYS a, LTL_ALWAYS b), c))``;



CONGRUENCE_SIMP_CONV ``LTL_EQUIVALENT`` ltl_nnf_cs std_ss [] ltl6;

(*Additional definitions may be used*)
CONGRUENCE_SIMP_CONV ``LTL_EQUIVALENT`` ltl_nnf_cs std_ss [LTL_ALWAYS_PALWAYS_ALTERNATIVE_DEFS, LTL_EVENTUAL_def] ltl6;


(*Even if simplifing to EQ the EQ-Rules in the congset are used,
  in this case the Definition of LTL_SWHILE is used *)
CONGRUENCE_EQ_SIMP_CONV ltl_nnf_cs std_ss [] ltl4;
SIMP_CONV std_ss [LTL_SWHILE_def] ltl4;

(*However, simplifing with respect to an other relation is much more useful*)
CONGRUENCE_SIMP_CONV ``LTL_EQUIVALENT`` ltl_nnf_cs std_ss [] ltl4


(*CONGRUENCE_SIMP_CONV never fails,
  CONGRUENCE_SIMP_QCONV may fail*)
CONGRUENCE_SIMP_CONV ``LTL_EQUIVALENT`` ltl_nnf_cs std_ss [] ltl2;
CONGRUENCE_SIMP_QCONV ``LTL_EQUIVALENT`` ltl_nnf_cs std_ss [] ltl2;

*)