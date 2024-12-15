structure ltl2omega :> ltl2omega =
struct

open HolKernel Parse boolLib bossLib;

open full_ltlTheory arithmeticTheory automaton_formulaTheory xprop_logicTheory prop_logicTheory
     infinite_pathTheory tuerk_tacticsLib symbolic_semi_automatonTheory listTheory pred_setTheory
     temporal_deep_mixedTheory pred_setTheory rich_listTheory set_lemmataTheory pairTheory rltlTheory
     ltl_to_automaton_formulaTheory numLib listLib translationsLib
     rltl_to_ltlTheory psl_to_rltlTheory UnclockedSemanticsTheory
     SyntacticSugarTheory congLib temporal_deep_simplificationsLib;

open testutils;

(* A function to generate test ltl formulas.
   This has been kindly provided by Kristin Yvonne Rozier <kyrozier@cs.rice.edu>

   Input: n = the number of bits in the counter
   Output: an LTL formula describing an n-bit counter
 *)
local
  fun mpattern_int 0 = ``LTL_NEXT (m:'a ltl)``
    | mpattern_int n = subst [mk_var ("X", ``:'a ltl``) |-> mpattern_int (n-1)]
                          ``LTL_NEXT (LTL_AND(LTL_NOT (m:'a ltl), X))``;

  fun mpattern n = subst [mk_var ("X", ``:'a ltl``) |-> mpattern_int n]
                        ``LTL_AND((m:'a ltl), LTL_ALWAYS (LTL_IMPL (m, X)))``;

  fun bpattern 0 = ``LTL_NOT (b:'a ltl)``
    | bpattern n = subst [mk_var ("X", ``:'a ltl``) |-> bpattern (n-1)]
                        ``LTL_AND(LTL_NOT (b:'a ltl), LTL_NEXT X)`` ;

  fun nest_next_pattern 0 t = t
    | nest_next_pattern n t = liteLib.mk_icomb (``LTL_NEXT:'a ltl->'a ltl``, nest_next_pattern (n-1) t)

  fun nest_pattern n =
    let
      val pattern = ``LTL_AND (
                        LTL_ALWAYS (LTL_IMPL(
                          LTL_AND(m:'a ltl, LTL_NOT b),
                          LTL_NEXT (LTL_AND (X1,
                            LTL_SUNTIL(
                              LTL_AND (LTL_NOT m, LTL_AND(LTL_IMPL (b, LTL_NEXT X1),
                                  LTL_IMPL (LTL_NOT b, LTL_NEXT X2))), m))))),
                        LTL_ALWAYS (LTL_IMPL(
                          LTL_AND(m:'a ltl, b),
                          LTL_NEXT (LTL_AND (X2,
                            LTL_OR (
                              LTL_SUNTIL(LTL_AND (b, LTL_AND(LTL_NOT m, LTL_NEXT (X2))), m),

                              LTL_AND (LTL_NOT m, LTL_AND(LTL_NOT b,
                              LTL_NEXT (LTL_AND(X1,
                                LTL_SUNTIL(
                                  LTL_AND (LTL_NOT m, LTL_AND(LTL_IMPL (b, LTL_NEXT (X1)),
                                  LTL_IMPL (LTL_NOT b, LTL_NEXT (X2)))), m)))))
                            ))))))``;


      val x1_term = nest_next_pattern n ``b:'a ltl``
      val x2_term = nest_next_pattern n ``LTL_NOT b:'a ltl``;
    in
      subst [mk_var ("X1", ``:'a ltl``) |-> x1_term,
            mk_var ("X2", ``:'a ltl``) |-> x2_term] pattern
    end;

in
  fun ltl_counter n =
    let
      val t1 = mpattern n;
      val t2 = bpattern n;
      val t3 = nest_pattern n;

      val pattern = ``LTL_AND((X1:'a ltl), LTL_AND(X2, X3))``
      val term = subst [mk_var ("X1", ``:'a ltl``) |-> t1,
                        mk_var ("X2", ``:'a ltl``) |-> t2,
                        mk_var ("X3", ``:'a ltl``) |-> t3] pattern

      val m = ``LTL_PROP(P_PROP (m:'a))``
      val b = ``LTL_PROP(P_PROP (b:'a))``;
      val term = subst [mk_var ("m", ``:'a ltl``) |-> m,
                        mk_var ("b", ``:'a ltl``) |-> b] term
    in
      term
    end
end;

val pslTerm = ``
    F_ALWAYS (F_IMPLIES (
                 F_STRONG_BOOL (B_PROP aa),
                 F_STRONG_NEXT_EVENT (B_PROP bb,
                                      F_STRONG_BEFORE (
                                            F_STRONG_BOOL (B_PROP cc),
                                            F_STRONG_BOOL (B_PROP dd)))))``;

val rltlTerm = (liteLib.mk_icomb (``PSL_TO_RLTL``, pslTerm));

val rltlTermEval = rhs (concl (
SIMP_CONV std_ss [PSL_TO_RLTL_def, F_ALWAYS_def, F_G_def,
                  F_F_def, BEXP_TO_PROP_LOGIC_def,
                  F_IMPLIES_def, F_OR_def,
                  F_STRONG_NEXT_EVENT_def,
                  F_STRONG_BEFORE_def] rltlTerm))

val ltlTerm = (liteLib.mk_icomb (``RLTL_TO_LTL P_FALSE P_FALSE``, rltlTermEval));
val ltlTermEval = rhs (concl (
  SIMP_CONV std_ss [RLTL_TO_LTL_def] ltlTerm))
val ltlTermSimp = rand ( concl (
  CONGRUENCE_SIMP_CONV ``LTL_EQUIVALENT`` ltl_nnf_cs std_ss [] ltlTermEval))

(* Example from "Construction Buechi Automata from Linear Temporal Logic Using
   Simulation Relations for Alternating Buechi Automata" by Carsten Fritz *)
val test0LTL = ``
    LTL_NOT
     (LTL_SUNTIL (LTL_SUNTIL (LTL_NEXT (LTL_PROP (P_PROP b)),
                              LTL_NOT (LTL_SUNTIL (LTL_NOT (LTL_ALWAYS (LTL_PROP (P_PROP a))),
                                                   LTL_NOT (LTL_PROP (P_PROP  c))))),
                  LTL_NOT (LTL_SUNTIL (LTL_NOT (LTL_ALWAYS (LTL_NOT (LTL_PROP (P_PROP a)))),
                                       LTL_NOT (LTL_PROP (P_PROP a))))))``;

val test1LTL = ``LTL_PROP (P_PROP a)``;
val test2LTL = ``LTL_NOT(LTL_PROP (P_PROP a))``;
val test3LTL = ``LTL_NOT(LTL_NOT(LTL_PROP (P_PROP a)))``;
val test4LTL = ``LTL_AND(LTL_NOT(LTL_PROP (P_PROP a)), LTL_PROP (P_PROP b))``;
val test5LTL = ``LTL_OR(LTL_NOT(LTL_PROP (P_PROP a)), LTL_PROP (P_PROP b))``;
val test6LTL = ``LTL_NEXT(LTL_PROP (P_PROP a))``;
val test7LTL = ``LTL_PSNEXT(LTL_PROP (P_PROP a))``;
val test8LTL = ``LTL_SUNTIL (LTL_PROP (P_PROP a), LTL_NEXT(LTL_PROP (P_PROP a)))``;
val test9LTL = ``LTL_PSUNTIL (LTL_PROP (P_PROP a), LTL_PROP (P_PROP a))``;
val test10LTL = ``LTL_PSUNTIL (LTL_ALWAYS(LTL_PROP (P_PROP a)), LTL_PROP (P_PROP a))``;
val test11LTL = ``LTL_SUNTIL (LTL_ALWAYS(LTL_PROP (P_PROP a)), LTL_AND(LTL_PROP (P_PROP c), LTL_NEXT(LTL_PROP (P_PROP (b:'c)))))``;

val test12LTL = ``LTL_AND(LTL_NEXT(LTL_PROP (P_PROP (b))), LTL_NEXT(LTL_PROP (P_PROP (b))))``;

val test13LTL = ``
LTL_OR(
  LTL_AND(
    LTL_PSUNTIL
      (LTL_NOT (LTL_SUNTIL (LTL_PROP P_TRUE,LTL_NOT (LTL_PROP (P_PROP a)))),
      LTL_PROP (P_PROP a)),
    LTL_PSUNTIL
      (LTL_NOT (LTL_SUNTIL (LTL_PROP P_TRUE,LTL_NOT (LTL_PROP (P_PROP b)))),
      LTL_PROP (P_PROP c))),
  LTL_AND(
      LTL_PSUNTIL
        (LTL_NOT (LTL_SUNTIL (LTL_PROP P_TRUE,LTL_NOT (LTL_PROP (P_PROP d)))),
        LTL_PROP (P_PROP e)),
      LTL_PSUNTIL
        (LTL_NOT (LTL_SUNTIL (LTL_PROP P_TRUE,LTL_NOT (LTL_PROP (P_PROP d)))),
        LTL_PROP (P_PROP b))))``;

val test14LTL = ``LTL_EQUIV(LTL_NOT(LTL_PROP (P_PROP a)), LTL_PROP (P_PROP b))``;

(* p U q *)
val test15LTL = ``LTL_SUNTIL (LTL_PROP (P_PROP p), LTL_PROP (P_PROP q))``;

val test1RLTL = ``RLTL_PROP (P_PROP a)``;
val test2RLTL = ``RLTL_NOT(RLTL_PROP (P_PROP (a:'c)))``;
val test3RLTL = ``RLTL_ACCEPT (RLTL_SUNTIL (RLTL_PROP (P_PROP a),
                                            RLTL_NEXT (RLTL_PROP (P_PROP a))), P_PROP c)``;

(* Some examples to execute at interactivly. Just change the
   number of the test terms or introduce on terms

   syntax: ltl2omega fast neg ltl
 *)
fun ltl2omega_test (test_fn, problem, result) = let
    val _ = tprint (term_to_string problem);
in
    require (check_result (aconv result o concl)) test_fn problem
end;

val test_cases =
   [(ltl2omega false (* no-fast *) false (* orig *), test15LTL (* p U q *),
     ``!sv.
          IS_ELEMENT_ITERATOR sv 1 {q; p} ==>
          !i.
              LTL_SEM i
                (LTL_SUNTIL (LTL_PROP (P_PROP p),LTL_PROP (P_PROP q))) <=>
              A_SEM i
                (A_UNIV
                   (symbolic_semi_automaton (\s. ?n. n < 1 /\ s = sv n)
                      (P_BIGAND [])
                      (XP_BIGAND
                         [XP_EQUIV
                            (XP_PROP (sv 0),
                             XP_OR
                               (XP_PROP q,
                                XP_AND (XP_PROP p,XP_NEXT_PROP (sv 0))))]),
                    A_IMPL (A_BIGAND [],ACCEPT_COND_PROP (P_PROP (sv 0)))))``),

    (ltl2omega false (* no-fast *) true (* neg *), test15LTL,
     ``!sv.
          IS_ELEMENT_ITERATOR sv 1 {q; p} ==>
          !i.
              LTL_SEM i
                (LTL_SUNTIL (LTL_PROP (P_PROP p),LTL_PROP (P_PROP q))) <=>
              A_SEM i
                (A_NDET
                   (symbolic_semi_automaton (\s. ?n. n < 1 /\ s = sv n)
                      (P_BIGAND [])
                      (XP_BIGAND
                         [XP_EQUIV
                            (XP_PROP (sv 0),
                             XP_OR
                               (XP_PROP q,
                                XP_AND (XP_PROP p,XP_NEXT_PROP (sv 0))))]),
                    A_AND
                      (A_BIGAND
                         [ACCEPT_COND_GF (P_IMPL (P_PROP (sv 0),P_PROP q))],
                       ACCEPT_COND_PROP (P_PROP (sv 0)))))``),

    (ltl2omega true (* fast *) false (* orig *), test15LTL,
     ``!sv.
          IS_ELEMENT_ITERATOR sv 1 {p; q} ==>
          !i.
              LTL_SEM i
                (LTL_SUNTIL (LTL_PROP (P_PROP p),LTL_PROP (P_PROP q))) <=>
              A_SEM i
                (A_UNIV
                   (symbolic_semi_automaton (\s. ?n. n < 1 /\ s = sv n)
                      (P_BIGAND [])
                      (XP_BIGAND
                         [XP_EQUIV
                            (XP_PROP (sv 0),
                             XP_OR
                               (XP_CURRENT (P_PROP q),
                                XP_AND
                                  (XP_CURRENT (P_PROP p),XP_NEXT_PROP (sv 0))))]),
                    A_IMPL (A_BIGAND [],ACCEPT_COND_PROP (P_PROP (sv 0)))))``),

    (ltl2omega true (* fast *) true (* neg *), test15LTL,
     ``!sv.
          IS_ELEMENT_ITERATOR sv 1 {p; q} ==>
          !i.
              LTL_SEM i
                (LTL_SUNTIL (LTL_PROP (P_PROP p),LTL_PROP (P_PROP q))) <=>
              A_SEM i
                (A_NDET
                   (symbolic_semi_automaton (\s. ?n. n < 1 /\ s = sv n)
                      (P_BIGAND [])
                      (XP_BIGAND
                         [XP_EQUIV
                            (XP_PROP (sv 0),
                             XP_OR
                               (XP_CURRENT (P_PROP q),
                                XP_AND
                                  (XP_CURRENT (P_PROP p),XP_NEXT_PROP (sv 0))))]),
                    A_AND
                      (A_BIGAND
                         [ACCEPT_COND_GF (P_IMPL (P_PROP (sv 0),P_PROP q))],
                       ACCEPT_COND_PROP (P_PROP (sv 0)))))``),

    (ltl2omega_rewrite true (* max *), test15LTL,
     ``!sv.
          IS_ELEMENT_ITERATOR sv 1 {p; q} ==>
          !i.
              LTL_SEM i
                (LTL_SUNTIL (LTL_PROP (P_PROP p),LTL_PROP (P_PROP q))) <=>
              A_SEM i
                (A_NDET
                   (symbolic_semi_automaton (\s. ?n. n < 1 /\ s = sv n)
                      P_TRUE
                      (XP_AND
                         (XP_EQUIV
                            (XP_PROP (sv 0),
                             XP_OR
                               (XP_PROP q,
                                XP_AND (XP_PROP p,XP_NEXT_PROP (sv 0)))),
                          XP_TRUE)),
                    A_AND
                      (A_AND
                         (ACCEPT_COND_GF (P_IMPL (P_PROP (sv 0),P_PROP q)),
                          A_TRUE),ACCEPT_COND_PROP (P_PROP (sv 0)))))``),

    (ltl2omega_rewrite false (* min *), test15LTL,
     ``!sv.
          IS_ELEMENT_ITERATOR sv 1 {p; q} ==>
          !i.
              LTL_SEM i
                (LTL_SUNTIL (LTL_PROP (P_PROP p),LTL_PROP (P_PROP q))) <=>
              A_SEM i
                (A_UNIV
                   (symbolic_semi_automaton (\s. ?n. n < 1 /\ s = sv n)
                      P_TRUE
                      (XP_AND
                         (XP_EQUIV
                            (XP_PROP (sv 0),
                             XP_OR
                               (XP_PROP q,
                                XP_AND (XP_PROP p,XP_NEXT_PROP (sv 0)))),
                          XP_TRUE)),
                    A_IMPL (A_TRUE,ACCEPT_COND_PROP (P_PROP (sv 0)))))``)];

val _ = List.app (ignore o ltl2omega_test) test_cases;

(* simplified tests, only make sure the test raise no exception *)
fun ltl2omega_test_simple (test_fn, problem) = let
    val _ = tprint (term_to_string problem);
in
    require (check_result (fn th => true)) test_fn problem
end;

(*
************************************************
The fast switch has some influence. Notice the
different number of needed state vars and the
different needed time
************************************************

time (ltl2omega true true) test13LTL
time (ltl2omega false true) test13LTL

time (ltl2omega true true) test0LTL
time (ltl2omega false true) test0LTL
*)

val test_cases_simple =
   [(ltl2omega false false, test0LTL),
    (ltl2omega true  false, test0LTL),
    (ltl2omega false false, test1LTL),
    (ltl2omega false false, test2LTL),
    (ltl2omega false false, test3LTL),
    (ltl2omega false false, test4LTL),
    (ltl2omega false false, test5LTL),
    (ltl2omega false false, test6LTL),
    (ltl2omega false false, test7LTL),
    (ltl2omega false false, test8LTL),
    (ltl2omega false false, test9LTL),
    (ltl2omega false false, test10LTL),
    (ltl2omega false false, test11LTL),
    (ltl2omega false false, test12LTL),
    (ltl2omega false false, test13LTL),
    (ltl2omega true  false, test13LTL)];

val _ = List.app (ignore o ltl2omega_test_simple) test_cases_simple;

(*
************************************************
Internal view. The fast version keeps just one
binding. The slow one keeps all
************************************************

NOTE: val (b1, b2) = if neg then (true, false) else (false, true);

ltl2omega_internal true  (* fast *) false (* b1 *) true (* b2 *) test11LTL
ltl2omega_internal false (* slow *) false (* b1 *) true (* b2 *) test11LTL
 *)

val test_cases_simple2 =
   [(ltl2omega_internal true  (* fast *) false (* b1 *) true (* b2 *), test11LTL),
    (ltl2omega_internal false (* slow *) false (* b1 *) true (* b2 *), test11LTL)
    ];

val _ = List.app (ignore o ltl2omega_test_simple) test_cases_simple2;

(*
************************************************
A simple, non optimised translation that uses
just rewriting. Just a proof of concept
************************************************
time (ltl2omega_rewrite true) test11LTL
 *)

(*
************************************************
Translations to kripke_structure
************************************************

time (ltl_contradiction2ks_fair_emptyness true) test11LTL
time (ltl_contradiction2ks_fair_emptyness___num 1 true) test11LTL
time (ltl_contradiction2ks_fair_emptyness___num 2 true) test11LTL
time (ltl_contradiction2ks_fair_emptyness___num 3 true) test11LTL

time (ltl_contradiction2ks_fair_emptyness true) test13LTL
time (ltl_contradiction2ks_fair_emptyness___num 1 true) test13LTL
time (ltl_contradiction2ks_fair_emptyness___num 2 true) test13LTL
time (ltl_contradiction2ks_fair_emptyness___num 3 true) test13LTL
 *)

val test_cases_simple3 =
   [(ltl_contradiction2ks_fair_emptyness true, test11LTL),
    (ltl_contradiction2ks_fair_emptyness true, test13LTL)];

val _ = List.app (ignore o ltl2omega_test_simple) test_cases_simple3;

val test_cases_simple4 =
   [(ltl_contradiction2ks_fair_emptyness___num 1 true, test11LTL),
    (ltl_contradiction2ks_fair_emptyness___num 2 true, test11LTL),
    (ltl_contradiction2ks_fair_emptyness___num 3 true, test11LTL),
    (ltl_contradiction2ks_fair_emptyness___num 1 true, test13LTL),
    (ltl_contradiction2ks_fair_emptyness___num 2 true, test13LTL),
    (ltl_contradiction2ks_fair_emptyness___num 3 true, test13LTL)];

val _ = List.app (ignore o ltl2omega_test_simple) test_cases_simple4;

(*
val ltl_ks_sem2ks_fair_emptyness___no_ks : bool -> term -> thm
val ltl_ks_sem2ks_fair_emptyness : bool -> term -> term -> thm
val ltl_equivalent2ks_fair_emptyness : bool -> term -> term -> thm
 *)

(*
*************************************************
LTL counters
These can be used to test performance on
huge formulas. Additionally these formulas contain
large subterms several times. Thus they benefit from
using the "slow" version
*************************************************

time (ltl2omega false true) (ltl_counter 2)
time (ltl2omega true true) (ltl_counter 2)
 *)

val test_cases_ltl_counter =
   [(ltl2omega false true, ltl_counter 2),
    (ltl2omega true  true, ltl_counter 2)];

val _ = List.app (ignore o ltl2omega_test_simple) test_cases_ltl_counter;

(*
************************************************
You may also be interested in the following
definitions and theorems
************************************************

IS_ELEMENT_ITERATOR_def
IS_ELEMENT_ITERATOR_0
IS_ELEMENT_ITERATOR_EXISTS
LTL_TO_GEN_BUECHI_DS___SEM___TRUE
LTL_TO_GEN_BUECHI_DS___SEM___FALSE

LTL_TO_GEN_BUECHI_DS___SEM_def
LTL_TO_GEN_BUECHI_DS___FAIR_RUN_def
LTL_TO_GEN_BUECHI_DS___BINDING_RUN_def
LTL_TO_GEN_BUECHI_DS___MIN_FAIR_RUN_def
LTL_TO_GEN_BUECHI_DS___MAX_FAIR_RUN_def
*)

end
