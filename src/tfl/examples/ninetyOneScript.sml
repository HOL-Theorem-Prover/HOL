(*---------------------------------------------------------------------------
           McCarthy's 91 function.
 ---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib
open Defn TotalDefn numLib prim_recTheory arithmeticTheory;

(*---------------------------------------------------------------------------
       Define the 91 function. We call it "N". We use Hol_defn to
       make the definition, since we have to tackle the termination
       proof ourselves.
 ---------------------------------------------------------------------------*)

val _ = new_theory "ninetyOne"

val N_defn = Hol_defn "N" ‘N(x) = if x>100 then x-10 else N (N (x+11))’;

val [Neqn] = Defn.eqns_of N_defn;
val SOME Nind = Defn.ind_of N_defn;

val SOME N_aux_defn = Defn.aux_defn N_defn;
val SOME N_aux_ind = Defn.ind_of N_aux_defn;
val [E] = map DISCH_ALL (Defn.eqns_of N_aux_defn);

(*---------------------------------------------------------------------------
      Prove partial correctness for N, to see how such a proof
      works when the termination relation has not yet been supplied.
 ---------------------------------------------------------------------------*)

val Npartly_correct = Q.prove
(‘WF R /\
  (!x. ~(x > 100) ==> R (N_aux R (x + 11)) x) /\
  (!x. ~(x > 100) ==> R (x + 11) x)
    ==>
  !n. N(n) = if n>100 then n-10 else 91’,
 STRIP_TAC THEN recInduct Nind
   THEN RW_TAC arith_ss []
   THEN ONCE_REWRITE_TAC [Neqn]
   THEN RW_TAC arith_ss []);

val N_aux_partial_correctness = Q.prove
(‘WF R /\
  (!x. ~(x > 100) ==> R (N_aux R (x + 11)) x) /\
  (!x. ~(x > 100) ==> R (x + 11) x)
    ==>
  !n. N_aux R n = if n>100 then n-10 else 91’,
 STRIP_TAC THEN recInduct N_aux_ind
   THEN RW_TAC arith_ss []
   THEN RW_TAC arith_ss [E]);

(*---------------------------------------------------------------------------*)
(* Termination of 91 is a bit tricky.                                        *)
(*---------------------------------------------------------------------------*)

val lem = DECIDE “~(x > 100) ==> (101-y < 101-x <=> x<y)”;

val unexpand_measure = Q.prove
(‘(\x' x''. 101 < x' + (101 - x'') /\ x'' < 101) = measure \x. 101-x’,
 RW_TAC arith_ss [FUN_EQ_THM, measure_thm]);

(*---------------------------------------------------------------------------*)
(* Get the auxiliary rec. eqns, instantiate with termination relation, and   *)
(* do some simplifications.                                                  *)
(*---------------------------------------------------------------------------*)

val condE =
  SIMP_RULE arith_ss [AND_IMP_INTRO,WF_measure,measure_thm,SUB_LEFT_LESS]
        (Q.INST [‘R’ |-> ‘measure \x. 101-x’] E);

val correctness' =
  SIMP_RULE arith_ss [WF_measure,measure_thm,SUB_LEFT_LESS]
        (Q.INST [‘R’ |-> ‘measure \x. 101-x’] (N_aux_partial_correctness));

val N_aux_ind' = (* takes ages, because of subtraction? *)
  SIMP_RULE arith_ss [WF_measure,measure_thm,SUB_LEFT_LESS]
        (Q.INST [‘R’ |-> ‘measure \x. 101-x’] (DISCH_ALL N_aux_ind));

(*---------------------------------------------------------------------------*)
(* Termination. This is done the hard way, to prop up an obscure point.      *)
(* We'll use NA to abbreviate the instantiated auxiliary function: thus      *)
(* NA = N_aux(measure($- 101)). The proof goes as follows:                   *)
(*                                                                           *)
(* Induct on the termination relation, then tidy up the goal, obtaining the  *)
(* goal "x < NA (x+11)". We now want to unroll NA(x+11). This requires       *)
(* manually instantiating the auxiliary fn with `x+11`, and proving its      *)
(* constraints. One of these is                                              *)
(*                                                                           *)
(*   x+11 < NA (x+22)           (%%)                                         *)
(*                                                                           *)
(* We will prove this by using the IH, by means of first doing a case split  *)
(* on "x+11 > 100". Having (%%) allows NA(x+11) to be unrolled, but we will  *)
(* also keep (%%) around for later use. Now  conditional rewriting will      *)
(* unroll "NA(x+11)" yielding the goal "x < NA(NA(x+22))". Now we want to    *)
(* unroll NA one more time, at its argument NA(x+22). Again we do a case     *)
(* split, this time on "NA (x+22) > 100". Consider the two branches coming   *)
(* from the case split.                                                      *)
(* Case: NA (x+22) > 100. The goal is easy to prove by arithmetic            *)
(*       from the assumptions and unrolling NA into the base case.           *)
(* Case: ~(NA (x+22) > 100). Here the IH may be used with a somewhat clever  *)
(*       witness to deliver                                                  *)
(*       NA(x+22) -11 < NA(NA(x+22) -11+11)                                  *)
(*                    = NA(NA(x+22))                                         *)
(*       After that, the proof of this branch is also easy.                  *)
(*---------------------------------------------------------------------------*)

val (N_def,N_ind) = Defn.tprove
 (N_defn,
  WF_REL_TAC ‘measure \x. 101 - x’
    THEN RW_TAC arith_ss [SUB_LEFT_LESS,unexpand_measure]
    THEN Q.ABBREV_TAC ‘NA = N_aux (measure (\x. 101 - x))’
    THEN measureInduct_on ‘(\m. 101 - m) x’
    THEN STRIP_TAC THEN FULL_SIMP_TAC arith_ss [lem]
    THEN MP_TAC (Q.INST [‘x’ |-> ‘x+11’] condE)
    THEN RW_TAC arith_ss []  (* implicit case split *)
    THEN ‘x+11 < NA(x+22)’ by METIS_TAC[DECIDE“x<x+11”,DECIDE“x+11+11=x+22”]
    THEN RW_TAC std_ss [] THEN WEAKEN_TAC is_imp
    THEN MP_TAC (Q.INST [‘x’ |-> ‘NA(x+22)’] condE)
    THEN RW_TAC arith_ss [] (* implicit case split *)
    THEN ‘x < NA (x+22) - 11 /\ ~(NA (x + 22) - 11 > 100)’ by DECIDE_TAC
    THEN ‘NA(x+22) - 11 < NA(NA(x+22) - 11 + 11)’ by METIS_TAC[]
    THEN POP_ASSUM MP_TAC
    THEN FULL_SIMP_TAC arith_ss [DECIDE “x+y < p ==> ((p-y)+y = p)”]);

(*---------------------------------------------------------------------------
      Note that the above development is slightly cranky, since
      the partial correctness theorem has constraints remaining.
      These were addressed by the termination proof, but the
      constraints were proved and then thrown away.

      Now try some computations with N.
 ---------------------------------------------------------------------------*)

val results = map EVAL [
  “N 0”, “N 10”, “N 11”, “N 12”, “N 40”, “N 89”, “N 90” ,
  “N 99”, “N 100”, “N 101”, “N 102”, “N 127”]

(* ----------------------------------------------------------------------
    Alternative approach

    If you do CPS-conversion and then defunctionalisation of the
    continuations, you realise the continuations can just be natural
    numbers, leading to the definition below.

    Proving that *this* terminates requires a tricksy lexicographic
    order, one that embodies the idea that you're approaching the target
    value of 101 (reducing the distance between this and n), but which
    has to cope with parameter combinations that will never occur in
    evaluations that start "normally".

   ---------------------------------------------------------------------- *)

Definition NT_def:
  NT c n = if c = 0 then n
           else if 100 < n then NT (c - 1) (n - 10)
           else NT (c + 1) (n + 11)
Termination
  qexists_tac ‘inv_image ($< LEX $<)
                (λ(c,n). if n < 101 then let m = (101 - n) DIV 11
                                         in
                                           (c + m, 202 - 2 * n)
                         else if c = 0 then (c,n)
                         else if c = 1 /\ 101 < n then (c,n)
                         else if n <= 111 then (c - 1, 223 - 2 * n)
                         else (c,n))’ >>
  rpt strip_tac >> asm_simp_tac (srw_ss()) []
  >- (irule relationTheory.WF_inv_image >> irule pairTheory.WF_LEX >>
      simp[])
  >- (Cases_on ‘n + 11 < 101’ >> ASM_REWRITE_TAC[]
      >- (‘n < 101’ by simp[] >> simp[] >> simp[pairTheory.LEX_DEF] >>
          disj2_tac >>
          ‘101 - n = 11 + (90 - n)’ by simp[] >>
          pop_assum SUBST1_TAC >> simp[ADD_DIV_RWT]) >>
      ‘90 <= n’ by simp[] >>
      simp[pairTheory.LEX_DEF])
  >- (Cases_on ‘c <= 1’ >> asm_simp_tac (srw_ss())[pairTheory.LEX_DEF]
      >- (‘c = 1’ by simp[] >> simp[] >> rw[] >> gs[NOT_LESS, NOT_LESS_EQUAL] >>
          simp[DIV_EQ_X]) >>
      ‘1 < c’ by simp[] >> simp[] >>
      Cases_on ‘n < 111’ >> gs[NOT_LESS_EQUAL, NOT_LESS]
      >- (‘(111 - n) DIV 11 = 0’ by simp[LESS_DIV_EQ_ZERO] >> simp[]) >>
      Cases_on ‘n = 111’ >> simp[] >> rw[])
End

Theorem NT_THM:
  !c n. NT c n = if c = 0 then n
                 else if n <= 10 * c + 91 then 91
                 else n - c * 10
Proof
  recInduct NT_ind >> rpt strip_tac >> Cases_on ‘c=0’
  >- (fs[] >> simp[Once NT_def])
  >- (pop_assum (fn th => RULE_ASSUM_TAC $ SRULE[th] >> assume_tac th) >>
      Cases_on ‘100 < n’ >>
      pop_assum (fn th => RULE_ASSUM_TAC $ SRULE[th] >> assume_tac th) >>
      ONCE_REWRITE_TAC [NT_def] >>
      REWRITE_TAC[ASSUME “c <> 0”]
      >- (asm_simp_tac bool_ss [] >>
          qpat_x_assum ‘NT _ _ = _’ kall_tac >>
          simp[]) >> simp[])
QED

Theorem NT_FUNPOW:
  !c n. NT c n = FUNPOW (NT 1) c n
Proof
  Induct >> simp[NT_THM] >> simp[FUNPOW, NT_THM] >>
  pop_assum (assume_tac o GSYM) >> simp[] >>
  simp[NT_THM]
QED

Overload TrN = “NT 1”

(* looks just like the traditional nested-recursion definition:
     |- TrN n = if 100 < n then n - 10 else TrN (TrN (n + 11))
*)
Theorem TrN_recursive_characterisation =
        NT_def |> Q.SPECL [‘n’, ‘1’]
               |> SRULE[SPEC “2” NT_FUNPOW, SPEC “0” NT_FUNPOW]
               |> REWRITE_RULE[FUNPOW, TWO, ONE]
               |> REWRITE_RULE[GSYM ONE]

(* |- TrN n = if n <= 101 then 91 else n - 10 *)
Theorem TrN_thm = NT_THM |> Q.SPECL [‘1’, ‘n’] |> SRULE[]


val _ = export_theory()
