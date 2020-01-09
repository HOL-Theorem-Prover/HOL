open HolKernel Parse boolLib bossLib;

(* core HOL *)
open arithmeticTheory pred_setTheory listTheory rich_listTheory

(* computability/lambda *)
open churchnumTheory churchlistTheory recsetsTheory
open reductionEval

(* kolmogorov includes *)
open kolmog_complexTheory kraft_ineqTheory


val _ = new_theory "pfree_enumerable";

val TWO_TIMES_DIV = Q.prove(
  ‘(2 * n DIV 2 = n) ∧ (2 * n + 1) DIV 2 = n ∧ (2 * n + 2) DIV 2 = n + 1’,
  reverse (rpt conj_tac)
  >- (‘2 * n + 2 = 2 * (n + 1)’ by simp[LEFT_ADD_DISTRIB] >>
      simp[] >> metis_tac[MULT_DIV, DECIDE “0 < 2n”, MULT_COMM]) >>
  metis_tac[DIV_MULT, DECIDE “1 < 2n”, MULT_COMM, MULT_DIV, DECIDE “0 < 2n”]);
val _ = augment_srw_ss [rewrites [TWO_TIMES_DIV]];

val BIT2_smaller = Q.prove(
  ‘x ≠ 0 ∧ EVEN x ⇒ (x - 2) DIV 2 < x’,
  Cases_on ‘x’ >> simp[EVEN] >> rename [‘EVEN m’] >> Cases_on ‘m’ >>
  simp[EVEN,ADD1,DIV_LT_X]);
val BIT1_smaller = Q.prove(
  ‘x ≠ 0 ⇒ (x - 1) DIV 2 < x’,
  Cases_on ‘x’ >> simp[ADD1, DIV_LT_X]);

val pfree_idx_def = Define‘
  pfree_idx i = prefix_free { bl | ∃y. Phi i (bl2n bl) = SOME y}
’;

val cnum_to_blist_def = Define‘
  cnum_to_blist =
    chap2$Y @@ LAM "f" (LAM "n" (
           ceqnat @@ church 0 @@ VAR "n" (* if n = 0 then ...*)
                  @@ cnil   (* nil, else... *)
                  @@ (ceven @@ VAR "n" (* if n EVEN then ... *)
                            @@ (ccons
                                  @@ cB T
                                  @@ (VAR "f" @@ (
                                         cdiv
                                           @@ (cminus @@ VAR "n" @@ church 2)
                                           @@ church 2
                                       )
                                     )
                               )
                            @@ (ccons
                                  @@ cB F
                                  @@ (VAR "f" @@ (
                                         cdiv
                                           @@ (cminus @@ VAR "n" @@ church 1)
                                           @@ church 2
                                       )
                                     )
                               )
                     )
         ))
’;

val cnum_to_blist_eqn = brackabs.brackabs_equiv [] cnum_to_blist_def

Theorem cnum_to_blist_behaviour:
  cnum_to_blist @@ church n ==
   if n = 0 then cnil
   else if EVEN n then
     ccons @@ cB T @@ (cnum_to_blist @@ church ((n - 2) DIV 2))
   else
     ccons @@ cB F @@ (cnum_to_blist @@ church ((n - 1) DIV 2))
Proof
  simp_tac (bsrw_ss()) [cnum_to_blist_eqn, Once chap2Theory.lameq_Y] >>
  Cases_on ‘n = 0’ >>
  asm_simp_tac (bsrw_ss()) [churchboolTheory.cB_behaviour, ceven_behaviour,
                            cminus_behaviour,
                            wh_ccons] >>
  Cases_on ‘EVEN n’ >>
  asm_simp_tac (bsrw_ss()) [churchboolTheory.cB_behaviour, ceven_behaviour,
                            cminus_behaviour, wh_ccons] >>
  simp_tac (bsrw_ss()) [
    MATCH_MP (chap2Theory.lameq_rules |> CONJUNCTS |> el 3) cnum_to_blist_eqn,
    Cong cvcons_cong
  ]
QED

Theorem cnum_to_blist_thm :
  cnum_to_blist @@ church n == cvlist (MAP cB (n2bl n))
Proof
  completeInduct_on ‘n’ >>
  simp_tac (bsrw_ss()) [Once cnum_to_blist_behaviour,
                        Once num_to_bool_list_def] >>
  Cases_on ‘n = 0’ >> simp[] >> Cases_on ‘EVEN n’ >>
  asm_simp_tac (bsrw_ss()) [wh_ccons, Cong cvcons_cong,
                            BIT2_smaller, BIT1_smaller]
QED

val cbl2n_def = Define‘
  cbl2n = LAM "l" (
    VAR "l" @@ church 0
        @@ LAM "h" (LAM "t" (
             cplus @@ (cmult @@ church 2 @@ VAR "t")
                   @@ (VAR "h" @@ church 2 @@ church 1)
                   ))
  )
’;

Theorem FV_cbl2n[simp]:
  FV cbl2n = ∅
Proof
  simp[cbl2n_def, EXTENSION]
QED

val cbl2n_eqn = brackabs.brackabs_equiv [] cbl2n_def

Theorem cbl2n_behaviour :
  cbl2n @@ cnil == church 0 ∧
  cbl2n @@ cvcons h t == cplus @@ (cmult @@ church 2 @@ (cbl2n @@ t))
                               @@ (h @@ church 2 @@ church 1)
Proof
  simp_tac (bsrw_ss()) [cbl2n_eqn, cnil_def, wh_cvcons]
QED

Theorem cbl2n_thm:
  cbl2n @@ cvlist (MAP cB bl) == church (bl2n bl)
Proof
  Induct_on ‘bl’ >>
  asm_simp_tac (bsrw_ss()) [cbl2n_behaviour, bool_list_to_num_def] >>
  Cases_on ‘h’ >> simp_tac (bsrw_ss() ++ ARITH_ss) []
QED

val bitstrings_def = Define‘
  (bitstrings 0 = [[]]) ∧
  (bitstrings (SUC n) = MAP (CONS T) (bitstrings n) ++ MAP (CONS F) (bitstrings n))
’;

val lenbl_eq = Q.prove(
  ‘LENGTH bl = SUC n ⇔
     (∃bl0. bl = T::bl0 ∧ LENGTH bl0 = n) ∨
     (∃bl0. bl = F::bl0 ∧ LENGTH bl0 = n)’,
  Cases_on ‘bl’ >> simp[] >> metis_tac[]);

Theorem bitstrings_correct:
  set (bitstrings n) = { bl | LENGTH bl = n }
Proof
  Induct_on ‘n’ >> simp[bitstrings_def, LIST_TO_SET_MAP, lenbl_eq] >>
  ‘∀b s. IMAGE (CONS (b:bool)) s = { bl | ∃bl0. bl = b :: bl0 /\ bl0 ∈ s }’
     by simp[EXTENSION] >> simp[]
QED

val cbitstrings_def = Define‘
  cbitstrings = LAM "n" (
    VAR "n"
        @@ cvcons cnil cnil
        @@ LAM "r" (
             cappend
               @@ (cmap @@ (ccons @@ cB T) @@ VAR "r")
               @@ (cmap @@ (ccons @@ cB F) @@ VAR "r")
           )
  )
’;

Theorem FV_cbitstrings[simp]:
  FV cbitstrings = ∅
Proof
  simp[EXTENSION, cbitstrings_def]
QED

val cbitstrings_eqn = brackabs.brackabs_equiv [] cbitstrings_def

Theorem cbitstrings_behaviour :
  cbitstrings @@ church 0 == cvlist [cnil] ∧
  cbitstrings @@ church (SUC n) ==
    cappend @@ (cmap @@ (ccons @@ cB T) @@ (cbitstrings @@ church n))
            @@ (cmap @@ (ccons @@ cB F) @@ (cbitstrings @@ church n))
Proof
  simp_tac (bsrw_ss()) [cbitstrings_eqn]
QED

Theorem LENGTH_bitstrings[simp]:
  LENGTH (bitstrings i) = 2 ** i
Proof
  Induct_on ‘i’ >> simp[bitstrings_def, EXP]
QED

Theorem cbitstrings_thm :
  cbitstrings @@ church n == cvlist (MAP (cvlist o MAP cB) (bitstrings n))
Proof
  Induct_on ‘n’ >>
  asm_simp_tac(bsrw_ss()) [cbitstrings_behaviour, bitstrings_def, cmap_cvlist,
                           cappend_cvlist, MAP_MAP_o, combinTheory.o_DEF] >>
  irule cvlist_LIST_REL_cong >> simp[LIST_REL_EL_EQN] >>
  qx_gen_tac ‘i’ >> strip_tac >> Cases_on ‘i < 2 ** n’ >>
  simp[EL_APPEND1, EL_APPEND2, EL_MAP] >>
  simp_tac (bsrw_ss()) [wh_ccons]
QED

(* prefix-free enumerator given index j and argument x
     dovetail over
       all prefixes of x, x itself and all strings that have x as a prefix.
   If a termination is found on string not equal to x then loop.
   If termination is found on x, return that.
*)

(*
val pfree_enumerator_def = Define‘
  pfree_enumerator =
  LAMl ["j"; "x"] (
    LAM "run" (
    ) @@
    LAM "i"

  )
’;
*)

(*
Theorem pfree_re:
  re { i | pfree_idx i}
Proof
  simp[re_def,pfree_idx_def] >>
  qexists_tac ‘
    dBnum (fromTerm (LAM "j" (* machine number *)

*)

val _ = export_theory();
