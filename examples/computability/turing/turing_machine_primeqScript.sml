open HolKernel Parse boolLib bossLib finite_mapTheory;
open recursivefnsTheory;
open prnlistTheory;
open primrecfnsTheory;
open listTheory;
open arithmeticTheory;
open numpairTheory;
open nlistTheory;
open pred_setTheory;
open turing_machineTheory;
open whileTheory
open logrootTheory;

val _ = new_theory "turing_machine_primeq";

Triviality DISJ_IMP_EQ[simp]:
  ((x = y) ∨ P ⇔ (x ≠ y ⇒ P)) ∧
  (P ∨ (x = y) ⇔ (x ≠ y ⇒ P)) ∧
  (x ≠ y ∨ P ⇔ ((x = y) ⇒ P)) ∧
  (P ∨ x ≠ y ⇔ ((x = y) ⇒ P))
Proof
  METIS_TAC []
QED

Definition updn_def:
  (updn [] = 0) ∧
  (updn [x] = tri x) ∧
  (updn [x;y] =  if y = 0 then tri x
                 else if y = 1 then tri (x + 2) + 2
                 else if y = 2 then tri x
                 else nB (y = 3) * tri x) ∧
  (updn [s;actn;tmn] =
   let tape = (nsnd tmn) in
   let tl = (nfst tape) in
   let th = ((nsnd tape) MOD 2) in
   let tr = ((nsnd tape) DIV 2) in
       if actn = 0 then (* Write 0 *)
           s *, (tl *, ((2 * tr)))
       else if actn = 1 then (* Write 1 *)
           s *, (tl *, ((2 * tr) + 1 ))
       else if actn = 2 then (* Move left *)
           if tl MOD 2 = 1 then
               s *, (((tl-1) DIV 2) *, ((2 * (th + (2 * tr))) + 1))
           else
               s *, ((tl DIV 2) *, (2 * (( th + (2 * tr)))))
       else if actn = 3 then  (* Move right *)
           if tr MOD 2 = 1 then
               s *, ((th + (2 * tl)) *, ((2 * ((tr-1) DIV 2)) + 1))
           else
               s *, ((th + (2 * tl)) *, (2 * (tr DIV 2)))
       else tmn) ∧
        (updn (s::actn::tmn::a::b) = updn [s;actn;tmn])
End

Theorem UPDATE_TM_NUM_act0_lem:
  ∀ s tmn actn.
    (actn = 0) ==>
    (updn [s;actn;tmn] =
     ⟦UPDATE_ACT_S_TM s (NUM_TO_ACT actn) (FULL_DECODE_TM tmn)⟧)
Proof
  REWRITE_TAC [updn_def] >> rpt strip_tac >>
   (* actn = 0*)
  simp[NUM_TO_ACT_def] >> rw[FULL_DECODE_TM_def,FULL_ENCODE_TM_def]
  >- (rw[UPDATE_ACT_S_TM_def] >> EVAL_TAC) >>
  rw[ENCODE_TM_TAPE_def]
  >- (rw[UPDATE_ACT_S_TM_def] >> rw[DECODE_TM_TAPE_def] >>
      simp[ENCODE_DECODE_thm])
  >- (rw[UPDATE_ACT_S_TM_def] >> rw[DECODE_TM_TAPE_def] >>
      simp[ENCODE_DECODE_thm ] >>
      `ODD (nsnd (nsnd tmn))` by metis_tac[EVEN_OR_ODD] >>
      fs[ODD_DIV_2_lem]) >>
  `(UPDATE_ACT_S_TM s Wr0
             <|state := nfst tmn;
               tape_l := FST (DECODE_TM_TAPE (nsnd tmn));
               tape_h := FST (SND (DECODE_TM_TAPE (nsnd tmn)));
               tape_r := SND (SND (DECODE_TM_TAPE (nsnd tmn)))|>).tape_h = Z`
       by fs[WRITE_0_HEAD_lem] >>
  rfs[]
QED


Theorem UPDATE_TM_NUM_act1_lem:
  ∀ s tmn actn.
    (actn = 1) ==>
    (updn [s;actn;tmn] =
     ⟦UPDATE_ACT_S_TM s (NUM_TO_ACT actn) (FULL_DECODE_TM tmn)⟧)
Proof
  REWRITE_TAC [updn_def] >> rpt strip_tac >>
  simp[NUM_TO_ACT_def] >>
  rw[FULL_DECODE_TM_def] >> rw[FULL_ENCODE_TM_def]
  >- (rw[UPDATE_ACT_S_TM_def] >> EVAL_TAC) >>
  rw[ENCODE_TM_TAPE_def]
  >- (rw[UPDATE_ACT_S_TM_def] >> rw[DECODE_TM_TAPE_def] >>
      simp[ENCODE_DECODE_thm])
  >- (`(UPDATE_ACT_S_TM s Wr1
             <|state := nfst tmn;
               tape_l := FST (DECODE_TM_TAPE (nsnd tmn));
               tape_h := FST (SND (DECODE_TM_TAPE (nsnd tmn)));
               tape_r := SND (SND (DECODE_TM_TAPE (nsnd tmn)))|>).tape_h = O`
        by fs[WRITE_1_HEAD_lem] >> `O=Z` by fs[] >> fs[])
   >- (rw[UPDATE_ACT_S_TM_def] >> rw[DECODE_TM_TAPE_def] >>
       simp[ENCODE_DECODE_thm ]) >>
   rw[UPDATE_ACT_S_TM_def] >> rw[DECODE_TM_TAPE_def] >>
   simp[ENCODE_DECODE_thm]
QED

Theorem UPDATE_TM_NUM_act2_lem:
  ∀ s tmn actn.
    (actn = 2) ==>
    (updn [s;actn;tmn] =
     ⟦UPDATE_ACT_S_TM s (NUM_TO_ACT actn) (FULL_DECODE_TM tmn)⟧)
Proof
  REWRITE_TAC [updn_def] >> rpt strip_tac >>
  simp[NUM_TO_ACT_def, FULL_DECODE_TM_def, FULL_ENCODE_TM_def,
       UPDATE_ACT_S_TM_def] >>
  rw[]
  >- (fs[])
  >- (`~EVEN (nfst (nsnd tmn))` by metis_tac[MOD_2, DECIDE ``0n <> 1``] >>
      `ODD (nfst (nsnd tmn))` by metis_tac[EVEN_OR_ODD] >>
      simp[ENCODE_TM_TAPE_def, ODD_TL_DECODE_lem, ENCODE_DECODE_thm] >>
      rw[ENCODE_def, ENCODE_DECODE_thm,DECODE_TM_TAPE_def] >> rfs[ODD_HD_DECODE]
      >- metis_tac[MOD_2]
      >- (rw[MOD_2] >> metis_tac[ODD_DIV_2_lem, EVEN_OR_ODD]))
  >- (simp[ENCODE_TM_TAPE_def, ODD_TL_DECODE_lem, ENCODE_DECODE_thm] >>
      rw[ENCODE_def,DECODE_TM_TAPE_def,ENCODE_DECODE_thm,MOD_2] >>
      metis_tac[ODD_DIV_2_lem, EVEN_OR_ODD])
  >- (`EVEN (nfst (nsnd tmn))` by metis_tac[MOD_2, DECIDE ``0n <> 1``] >>
      `~ODD (nfst (nsnd tmn))` by metis_tac[EVEN_AND_ODD] >>
      simp[ENCODE_TM_TAPE_def, EVEN_TL_DECODE_lem, ENCODE_DECODE_thm] >>
      rw[ENCODE_def,DECODE_TM_TAPE_def, ENCODE_DECODE_thm] >>
      rfs[EVEN_HD_DECODE]
      >- simp[MOD_2]
      >- (rw[MOD_2] >> metis_tac[ODD_DIV_2_lem, EVEN_OR_ODD]))
QED

Theorem UPDATE_TM_NUM_act3_lem:
  ∀ s tmn actn.
    (actn = 3) ==>
    (updn [s;actn;tmn] =
     ⟦UPDATE_ACT_S_TM s (NUM_TO_ACT actn) (FULL_DECODE_TM tmn)⟧)
Proof
  REWRITE_TAC [updn_def] >> rpt strip_tac >>
  simp[NUM_TO_ACT_def, FULL_DECODE_TM_def, FULL_ENCODE_TM_def,
       UPDATE_ACT_S_TM_def] >>
  rw[]
  >- (fs[SND_SND_DECODE_TM_TAPE])
  >- (simp[ENCODE_TM_TAPE_def, ENCODE_DECODE_thm] >>
      `~EVEN (nsnd (nsnd tmn) DIV 2)` by metis_tac[MOD_2, DECIDE ``0n <> 1``] >>
      `ODD (nsnd (nsnd tmn) DIV 2)` by metis_tac[EVEN_OR_ODD] >>
      rfs[SND_SND_DECODE_TM_TAPE] >> simp[ENCODE_def] >>
      fs[ODD_TL_DECODE_lem,ENCODE_DECODE_thm] >>
      `HD (DECODE (nsnd (nsnd tmn) DIV 2)) = O` by fs[ODD_HD_DECODE] >>
      simp[] >> rw[ENCODE_def,DECODE_TM_TAPE_def,ENCODE_DECODE_thm,MOD_2])
  >- (simp[ENCODE_TM_TAPE_def, ENCODE_DECODE_thm] >>
      `EVEN (nsnd (nsnd tmn) DIV 2)` by metis_tac[MOD_2, DECIDE ``0n <> 1``] >>
      `~ODD (nsnd (nsnd tmn) DIV 2)` by metis_tac[EVEN_AND_ODD] >>
      rfs[SND_SND_DECODE_TM_TAPE]  >>
      rw[ENCODE_def,DECODE_TM_TAPE_def, ENCODE_DECODE_thm,MOD_2] )
  >- (simp[ENCODE_TM_TAPE_def, ENCODE_DECODE_thm] >>
      `EVEN (nsnd (nsnd tmn) DIV 2)` by metis_tac[MOD_2, DECIDE ``0n <> 1``] >>
      fs[SND_SND_DECODE_TM_TAPE,EVEN_HD_DECODE] >>
      rw[ENCODE_def,DECODE_TM_TAPE_def, ENCODE_DECODE_thm,MOD_2] >>
      fs[EVEN_TL_DECODE_lem,ENCODE_DECODE_thm])
QED

Theorem UPDATE_TM_NUM_thm:
  ∀ s tmn actn.
    actn < 4 ==>
    (updn [s;actn;tmn] =
     ⟦UPDATE_ACT_S_TM s (NUM_TO_ACT actn) (FULL_DECODE_TM tmn)⟧)
Proof
  rpt strip_tac >>
  `(actn = 0) ∨ (actn = 1) ∨ (actn = 2) ∨ (actn = 3)` by simp[]
  >- (* actn = 0*)
     fs[UPDATE_TM_NUM_act0_lem]
  >-  (* actn = 1*)
     fs[UPDATE_TM_NUM_act1_lem]
  >- (* actn = 2*)
      fs[UPDATE_TM_NUM_act2_lem]
  >- (* actn = 3*)
      fs[UPDATE_TM_NUM_act3_lem]
QED

Definition pr3_def:  (pr3 f [] = f 0 0 0 : num) ∧
  (pr3 f [x:num] = f x 0 0) ∧
  (pr3 f [x;y] = f x y 0) ∧
  (pr3 f (x::y::z::t) = f x y z)
End

Triviality GENLIST1:
  GENLIST f 1 = [f 0]
Proof
  SIMP_TAC bool_ss [ONE, GENLIST, SNOC]
QED

Triviality GENLIST2:
  GENLIST f 2 = [f 0; f 1]
Proof
  SIMP_TAC bool_ss [TWO, ONE, GENLIST, SNOC]
QED

Triviality GENLIST3:
  GENLIST f 3 = [f 0; f 1; f 2]
Proof
  EVAL_TAC
QED

Theorem ternary_primrec_eq:
  primrec f 3 ∧ (∀n m p. f [n; m; p] = g n m p) ⇒ (f = pr3 g)
Proof
  SRW_TAC [][] >> SIMP_TAC (srw_ss()) [FUN_EQ_THM] >>
  Q.X_GEN_TAC `l` >>
  `(l = []) ∨ ∃n ns. l = n :: ns` by (Cases_on `l` >> SRW_TAC [][]) THENL [
    SRW_TAC [][] >>
    `f [] = f (GENLIST (K 0) 3)` by METIS_TAC [primrec_nil] >>
    SRW_TAC [][GENLIST3,pr3_def],

    `(ns = []) ∨ ∃m ms. ns = m::ms` by (Cases_on `ns` THEN SRW_TAC [][]) >>
    SRW_TAC [][] THENL [
      IMP_RES_THEN (Q.SPEC_THEN `[n]` MP_TAC) primrec_short >>
      SRW_TAC [][GENLIST1] >> EVAL_TAC,
      `(ms = []) ∨ ∃p ps. ms = p::ps` by (Cases_on `ms` THEN SRW_TAC [][]) >| [
        fs[pr3_def] >>
        `f [n;m] = f ([n;m] ++ GENLIST (K 0) (3 - LENGTH [n;m]))`
          by fs[primrec_short] >>
        `GENLIST (K 0) (3 - LENGTH [n;m]) = [0]` by EVAL_TAC >> rfs[],
        IMP_RES_THEN (Q.SPEC_THEN `(n::m::p::ps)` MP_TAC)
                     primrec_arg_too_long >>
        SRW_TAC [ARITH_ss][] >> fs[pr3_def]
      ]
    ]
  ]
QED

Theorem primrec_pr3:
  (∃g. primrec g 3 ∧ (∀m n p. g [m; n; p] = f m n p)) ⇒ primrec (pr3 f) 3
Proof
  METIS_TAC [ternary_primrec_eq]
QED

Definition MULT2_def:
  MULT2 x = 2*x
End

Definition pr_pr_up_case1_def:
  pr_pr_up_case1  =
  Cn (pr2 $*,) [ proj 0;Cn (pr2 $*,) [proj 2;Cn (pr1 MULT2) [proj 4]] ]
End

Theorem pr_up_case1_thm:
  ∀ x.
    (proj 0 x) *, (proj 2 x) *, (2 * (proj 4 x)) =
    Cn (pr2 $*,) [ proj 0;Cn (pr2 $*,) [proj 2;Cn (pr1 MULT2) [proj 4]] ] x
Proof
  strip_tac >> rfs[MULT2_def]
QED

Definition pr_pr_up_case2_def:
  pr_pr_up_case2  =
  Cn (pr2 $*,) [ proj 0;
                 Cn (pr2 $*,) [proj 2;Cn (succ) [Cn (pr1 MULT2) [proj 4]] ] ]
End

Definition pr_pr_up_case3_def:
  pr_pr_up_case3  =
  Cn (pr2 $*,) [ proj 0;Cn (pr2 $*,) [Cn (pr1 DIV2) [Cn (pr1 PRE) [proj 2]];
                                      Cn (succ) [Cn (pr1 MULT2) [Cn (pr2 (+)) [proj 3; Cn (pr1 MULT2) [proj 4]]]] ] ]
End

Definition pr_pr_up_case4_def:
  pr_pr_up_case4  =
  Cn (pr2 $*,) [ proj 0;Cn (pr2 $*,) [Cn (pr1 DIV2) [proj 2];
                                      Cn (pr1 MULT2) [Cn (pr2 (+)) [proj 3; Cn (pr1 MULT2) [proj 4]]] ] ]
End

Definition pr_pr_up_case5_def:
  pr_pr_up_case5  =
  Cn (pr2 $*,) [ proj 0;Cn (pr2 $*,) [Cn (pr2 (+)) [proj 3;Cn (pr1 MULT2) [proj 2]];
                                      Cn (succ) [Cn (pr1 MULT2) [Cn (pr1 DIV2) [Cn (pr1 PRE) [proj 4]]]] ] ]
End

Definition pr_pr_up_case6_def:
  pr_pr_up_case6  =
  Cn (pr2 $*,) [ proj 0;Cn (pr2 $*,) [Cn (pr2 (+)) [proj 3;Cn (pr1 MULT2) [proj 2]];
                                      Cn (pr1 MULT2) [Cn (pr1 DIV2) [proj 4]]]  ]
End

Definition pr_pr_up_case7_def:
  pr_pr_up_case7  =
  proj 5
End


Overload "onef" = ``K 1 : num list -> num``

Overload "twof" = ``K 2 : num list -> num``

Overload "threef" = ``K 3 : num list -> num``

Overload "fourf" = ``K 4 : num list -> num``

Triviality nB_cond_elim:
  nB p * x + nB (~p) * y = if p then x else y
Proof
  Cases_on `p` >> simp[]
QED


Theorem updn_zero_thm:
  ∀ x. updn [x;0] = updn [x]
Proof
  strip_tac >> fs[updn_def]
QED

Theorem updn_two_lem_1:
  ∀ x. ((x <> []) ∧ (LENGTH x <= 2)) ==> ( ∃ h. (x = [h])) ∨  (∃ h t. (x = [h;t]))
Proof
  rpt strip_tac >>  Cases_on `x` >- fs[] >> Cases_on `t` >- fs[] >> Cases_on `t'` >- fs[] >> rfs[]
QED

Theorem updn_two_lem_2:
  ∀x. (LENGTH x = 2) ==> (∃h t. (x = [h;t]))
Proof
  rpt strip_tac >>  Cases_on `x` >> fs[] >> Cases_on `t` >> fs[]
QED

Theorem updn_three_lem_1:
  ∀ x. ¬(LENGTH x <= 2) ==>
       (∃ a b c. (x = [a;b;c]) ) ∨ (∃ a b c d e. x = a::b::c::d::e)
Proof
  rpt strip_tac >>  Cases_on `x` >- fs[] >>
  rename [‘LENGTH (h::t)’] >> Cases_on ‘t’ >> fs[] >>
  rename [‘SUC (LENGTH l)’] >> Cases_on ‘l’ >> fs[] >>
  metis_tac[list_CASES]
QED

Theorem prim_pr_rec_updn:
  updn =
  Cn
    (pr_cond (Cn pr_eq [proj 1;zerof]) (pr_pr_up_case1) (
        pr_cond (Cn pr_eq [proj 1; onef]) (pr_pr_up_case2) (
          pr_cond (Cn pr_eq [proj 1; twof]) (
            pr_cond (Cn pr_eq [Cn (pr_mod) [proj 2;twof];onef])
                    (pr_pr_up_case3)
                    (pr_pr_up_case4)
          ) (
            pr_cond (Cn pr_eq [proj 1;threef]) (
              pr_cond (Cn pr_eq [Cn (pr_mod) [proj 4;twof];onef])
                      (pr_pr_up_case5)
                      (pr_pr_up_case6)
            ) (
              pr_cond (Cn pr_eq [proj 1;fourf])
                      (pr_pr_up_case7)
                      (pr_pr_up_case7)
            )
          )
        )
      )
    )
    [proj 0;proj 1; Cn (pr1 nfst) [Cn (pr1 nsnd) [proj 2]] ;
     Cn (pr_mod) [Cn (pr1 nsnd) [ Cn (pr1 nsnd) [proj 2]];twof];
     Cn (pr1 DIV2) [Cn (pr1 nsnd) [ Cn (pr1 nsnd) [proj 2]]]; proj 2 ]
Proof
  rw[Cn_def,FUN_EQ_THM]
  >> fs[pr_pr_up_case1_def,pr_pr_up_case2_def,pr_pr_up_case3_def,
         pr_pr_up_case4_def,pr_pr_up_case5_def,pr_pr_up_case6_def] >> rw[]
  >- (rw[proj_def,updn_def,updn_zero_thm,updn_three_lem_1] >> fs[]
      >- EVAL_TAC
      >- (`(∃h. x = [h]) ∨ (∃h t. x = [h;t])` by simp[updn_two_lem_1]
          >- (rw[updn_def] >> simp[MULT2_def] >> simp[npair_def])
          >- (fs[updn_def,updn_zero_thm] >> simp[MULT2_def] >>
              simp[npair_def]))
      >- (`(∃ a b c. x = [a;b;c]) ∨ (∃ a b c d e. x = (a::b::c::d::e))`
            by simp[updn_three_lem_1] >>
          fs[updn_def,MULT2_def,DIV2_def])
     )
  >- (fs[proj_def,updn_def,updn_zero_thm,pr_pr_up_case2_def] >> rw[] >> fs[]
      >- (`(∃h. x = [h]) ∨ (∃h t. x = [h;t])` by simp[updn_two_lem_1] >>
          fs[updn_def,updn_zero_thm] >> simp[MULT2_def, npair_def] >>
          EVAL_TAC >> simp[])
      >- (`(∃ a b c. x = [a;b;c]) ∨ (∃ a b c d e. x = (a::b::c::d::e))`
            by simp[updn_three_lem_1] >> fs[updn_def,MULT2_def,DIV2_def])
     )
  >- (fs[proj_def,updn_def,updn_zero_thm,pr_pr_up_case3_def] >> rw[] >> fs[] >>
      `(∃ a b c. x = [a;b;c]) ∨ (∃ a b c d e. x = (a::b::c::d::e))`
         by simp[updn_three_lem_1] >> fs[updn_def,MULT2_def,DIV2_def])
  >- (fs[proj_def,updn_def,updn_zero_thm,pr_pr_up_case4_def] >> rw[] >> fs[]
      >- (`(∃h. x = [h]) ∨ (∃h t. x = [h;t])` by simp[updn_two_lem_1] >>
          fs[updn_def,updn_zero_thm] >> simp[MULT2_def] >> simp[npair_def])
      >- (`(∃ a b c. x = [a;b;c]) ∨ (∃ a b c d e. x = (a::b::c::d::e))`
            by simp[updn_three_lem_1] >> fs[updn_def,MULT2_def,DIV2_def])
     )
  >- (fs[proj_def,updn_def,updn_zero_thm,pr_pr_up_case5_def] >> rw[] >> fs[] >>
      `(∃ a b c. x = [a;b;c]) ∨ (∃ a b c d e. x = (a::b::c::d::e))`
         by simp[updn_three_lem_1] >> fs[updn_def,MULT2_def,DIV2_def])
  >- (fs[proj_def,updn_def,updn_zero_thm,pr_pr_up_case6_def] >> rw[] >> fs[]
      >- (`(∃h. x = [h]) ∨ (∃h t. x = [h;t])` by simp[updn_two_lem_1] >>
          fs[updn_def] >> simp[MULT2_def] >> simp[npair_def])
      >- (`(∃ a b c. x = [a;b;c]) ∨ (∃ a b c d e. x = (a::b::c::d::e))`
           by simp[updn_three_lem_1] >> fs[updn_def,MULT2_def,DIV2_def])
     )
  >- (fs[proj_def,updn_def,updn_zero_thm,pr_pr_up_case7_def] >> rw[] >> fs[]

      >- (Cases_on ‘x = []’ >> fs[] >>
          `(∃h. x = [h]) ∨ (∃h t. x = [h;t])` by simp[updn_two_lem_1] >>
          fs[updn_def])
      >- (`(∃ a b c. x = [a;b;c]) ∨ (∃ a b c d e. x = (a::b::c::d::e))`
            by simp[updn_three_lem_1] >> fs[updn_def])
     )
QED

Triviality primrec_cn = List.nth(CONJUNCTS primrec_rules, 3)

Triviality primrec_pr = List.nth(CONJUNCTS primrec_rules, 4)

Theorem primrec_mult2:
  primrec (pr1 MULT2) 1
Proof
MATCH_MP_TAC primrec_pr1 >>
Q.EXISTS_TAC `Cn (pr2 $*) [proj 0; twof]` >> conj_tac >-
  SRW_TAC [][primrec_rules, alt_Pr_rule,Pr_thm,Pr_def ] >>
  SRW_TAC [][primrec_rules, alt_Pr_rule,Pr_thm,Pr_def ] >> rw[MULT2_def]
QED

Theorem primrec_div2:
  primrec (pr1 DIV2) 1
Proof
MATCH_MP_TAC primrec_pr1 >>
Q.EXISTS_TAC `Cn (pr_div) [proj 0; twof]` >> conj_tac >-
SRW_TAC [][primrec_rules, alt_Pr_rule,Pr_thm,Pr_def,primrec_pr_div ] >>
SRW_TAC [][primrec_rules, alt_Pr_rule,Pr_thm,Pr_def,primrec_pr_div ] >> rw[DIV2_def]
QED

Theorem primrec_pr_case1:
  primrec pr_pr_up_case1 6
Proof
SRW_TAC [][pr_pr_up_case1_def] >>
rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> rw[primrec_mult2]
QED

Theorem primrec_pr_case2:
  primrec pr_pr_up_case2 6
Proof
SRW_TAC [][pr_pr_up_case2_def] >>
        rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> rw[primrec_mult2]
QED

Theorem primrec_pr_case3:
  primrec pr_pr_up_case3 6
Proof
SRW_TAC [][pr_pr_up_case3_def] >>
        rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >>
        rw[primrec_mult2,primrec_div2]
QED

Theorem primrec_pr_case4:
  primrec pr_pr_up_case4 6
Proof
SRW_TAC [][pr_pr_up_case4_def] >>
        rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> rw[primrec_mult2,primrec_div2]
QED

Theorem primrec_pr_case5:
  primrec pr_pr_up_case5 6
Proof
SRW_TAC [][pr_pr_up_case5_def] >>
        rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> rw[primrec_mult2,primrec_div2]
QED

Theorem primrec_pr_case6:
  primrec pr_pr_up_case6 6
Proof
SRW_TAC [][pr_pr_up_case6_def] >>
        rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> rw[primrec_mult2,primrec_div2]
QED

Triviality primrec_proj = List.nth(CONJUNCTS primrec_rules, 2)

Theorem primrec_pr_case7:
  primrec pr_pr_up_case7 6
Proof
SRW_TAC [][pr_pr_up_case7_def] >>
      `5<6` by fs[]   >> SRW_TAC [][primrec_proj]
QED

Theorem UPDATE_TM_NUM_PRIMREC:
  primrec updn 3
Proof
SRW_TAC [][updn_def,primrec_rules,prim_pr_rec_updn] >> SRW_TAC [][pr_cond_def] >>
        rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules])
        >> fs[primrec_pr_case1,primrec_pr_case2,primrec_pr_case3,primrec_pr_case4,
               primrec_pr_case5,primrec_pr_case6,primrec_pr_case7,primrec_div2]
QED


Definition tmstepf_def:
  tmstepf p tmn =
     case OLEAST n. (nfst n, CELL_NUM (nsnd n)) ∈ FDOM p ∧ nfst n<>0 of
         NONE => 0 *, nsnd tmn
       | SOME n => let s = nfst n ;
                       sym = CELL_NUM (nsnd n) ;
                       (s',actn) = p ' (s,sym)
                   in
                     if nfst n = 0 then tmn
                     else if (nfst tmn = s) ∧
                             ((nsnd (nsnd tmn)) MOD 2 = NUM_CELL sym)
                     then updn [s'; ACT_TO_NUM actn; tmn]
                     else tmstepf (p \\ (s,sym)) tmn
Termination
  WF_REL_TAC `measure (CARD o FDOM o FST)` >> simp[OLEAST_EQ_SOME] >>
  metis_tac[MEMBER_CARD]
End

Theorem HEAD_DECODE_ENCDOE_EQ[simp]:
  (HD (DECODE (ENCODE t)) = Z) ==> (HD t = Z)
Proof
Cases_on `t`
  >- (EVAL_TAC)
  >- (fs[ENCODE_def,DECODE_def]  >> Cases_on `h` >> fs[] >> `2* ENCODE t' +1 = SUC (2* ENCODE t')` by fs[] >> rw[DECODE_def] >> rfs[ODD_DOUBLE] )
QED

Theorem ENCODE_ONE_TL_ZERO:
  (ENCODE t = 1) ==> (ENCODE (TL t) = 0)
Proof
Cases_on ` t` >> fs[] >- (EVAL_TAC) >- (fs[ENCODE_def] >> Cases_on `h` >> fs[])
QED

Theorem HD_DECODE_DOUBLED_EVEN[simp]:
  (x <> 0) ==> (HD (DECODE (2 * x)) = Z)
Proof
  Cases_on `x` >> fs[] >> `2*(SUC n) =SUC (SUC (2* n))` by simp[] >>
  simp[DECODE_def,ODD,ODD_MULT]
QED


Theorem TL_DECODE_DOUBLED_EVEN[simp]:
  (x <> 0) ==> (TL (DECODE (2 * x)) = DECODE x)
Proof
  Cases_on `x` >> fs[] >> `2 * (SUC n) =SUC (SUC (2* n))` by simp[] >>
  simp[DECODE_def,SimpLHS,ODD,ODD_MULT] >> pop_assum(SUBST1_TAC o SYM) >>
  fs[TWO_TIMES_DIV_TWO_thm]
QED

Theorem HD_DECODE_DOUBLED_ODD[simp]:
  (HD (DECODE (2 * x + 1)) = O)
Proof
  simp[GSYM(ADD1),DECODE_def,ODD,ODD_MULT]
QED


Theorem TL_DECODE_DOUBLED_ODD[simp]:
  TL (DECODE (2 * x + 1)) = DECODE x
Proof
  simp[GSYM ADD1,DECODE_def,ODD,ODD_MULT]
QED



Theorem ENCODED_DECODED_ENCODED_UPDATE_TM_thm:
  ⟦UPDATE_ACT_S_TM (FST (p ' (tm.state,tm.tape_h)))
                    (SND (p ' (tm.state,tm.tape_h))) (FULL_DECODE_TM ⟦tm⟧) ⟧ =
   ⟦(UPDATE_ACT_S_TM (FST (p ' (tm.state,tm.tape_h)))
                     (SND (p ' (tm.state,tm.tape_h))) (tm) )⟧
Proof
  fs[FULL_DECODE_TM_def,FULL_ENCODE_TM_def] >> rw[]
  >- (fs[ENCODE_TM_TAPE_def] >> Cases_on `tm.tape_h`
      >- (fs[SND_SND_DECODE_TM_TAPE_FULL] >>
          `EVEN (2 * ENCODE tm.tape_r)` by fs[EVEN_DOUBLE] >>
          fs[FST_SND_DECODE_TM_TAPE_FULL] >> fs[UPDATE_ACT_S_TM_def] >>
          Cases_on `SND (p ' (tm.state,Z))` >> fs[]
          >- (Cases_on `tm.tape_l = []` >> fs[ENCODE_def] >>
              Cases_on `ENCODE tm.tape_l = 0` >> fs[] )
          >- (Cases_on `tm.tape_r = []` >> fs[ENCODE_def] >>
              Cases_on `2* ENCODE tm.tape_r DIV 2 = 0` >> fs[]))
      >- (fs[SND_SND_DECODE_TM_TAPE_FULL] >>
          fs[UPDATE_ACT_S_TM_def] >>
          Cases_on `SND (p ' (tm.state,O))` >> fs[]
          >- (Cases_on `tm.tape_l = []` >> fs[ENCODE_def] >>
              Cases_on `ENCODE tm.tape_l = 0` >> fs[])
          >- (Cases_on `tm.tape_r = []` >> fs[ENCODE_def] >>
              Cases_on `(2 * ENCODE tm.tape_r + 1) DIV 2 = 0` >> fs[])))
  >- (fs[UPDATE_ACT_S_TM_def] >>
      Cases_on `SND (p ' (tm.state,tm.tape_h))` >> fs[]
         >- (simp[ENCODE_TM_TAPE_def,ENCODE_DECODE_thm] >> rw[] )
         >- (simp[ENCODE_TM_TAPE_def,ENCODE_DECODE_thm] >> rw[])
         >- (Cases_on `tm.tape_l` >> fs[ENCODE_def]
            >- (simp[ENCODE_TM_TAPE_def,ENCODE_DECODE_thm])
            >- (Cases_on `h` >> simp[]
               >- (rw[]
                  >- (simp[ENCODE_TM_TAPE_def,ENCODE_def])
                  >- (simp[ENCODE_TM_TAPE_def,ENCODE_def] >>
                      simp[ENCODE_DECODE_thm] ))
               >- (simp[ENCODE_TM_TAPE_def,ENCODE_DECODE_thm] ) ) )
         >- (Cases_on `tm.tape_r` >> fs[ENCODE_def]
             >- (simp[ENCODE_TM_TAPE_def,ENCODE_DECODE_thm])
             >- (Cases_on `h` >> simp[]
                 >- (rw[]
                     >- (simp[ENCODE_TM_TAPE_def,ENCODE_def])
                     >- (simp[ENCODE_TM_TAPE_def,ENCODE_def] >>
                         simp[ENCODE_DECODE_thm] ))
                 >- (simp[ENCODE_TM_TAPE_def,ENCODE_DECODE_thm] ) ) ))
QED


Theorem UPDATE_TM_NUM_corol:
  ∀s' tmn actn'. (updn [s'; ACT_TO_NUM actn'; tmn] =
                  ⟦UPDATE_ACT_S_TM s' actn' (FULL_DECODE_TM tmn)⟧)
Proof
fs[ACT_TO_NUM_LESS_4,UPDATE_TM_NUM_thm]
QED

Triviality lemma_11 =
    UPDATE_TM_ARB_Q |> Q.INST[`q` |-> `tm.prog` ]
                    |> SIMP_RULE(srw_ss())[tm_with_prog]

Theorem updn_UPDATE_TAPE:
  (tm.state, tm.tape_h) ∈ FDOM p ∧ tm.state <> 0 ==>
  ((λ(s',actn). updn [s'; ACT_TO_NUM actn; ⟦tm⟧]) (p ' (tm.state,tm.tape_h)) =
   ⟦UPDATE_TAPE (tm with prog := p)⟧)
Proof
  rw[] >> `ACT_TO_NUM actn < 4` by fs[ACT_TO_NUM_LESS_4] >>
  qabbrev_tac `ptm = tm with prog := p` >>
  `(tm.state,tm.tape_h) ∈ FDOM ptm.prog` by fs[Abbr`ptm`] >>
  `(ptm.state,ptm.tape_h) ∈ FDOM ptm.prog` by fs[Abbr`ptm`] >>
  `ptm.state <> 0` by simp[Abbr`ptm`] >>
  `(UPDATE_ACT_S_TM
      (FST (ptm.prog ' (ptm.state, ptm.tape_h)))
      (SND (ptm.prog ' (ptm.state,ptm.tape_h)))
      ptm =
    UPDATE_TAPE ptm)`
      by  fs[UPDATE_TAPE_ACT_STATE_TM_thm] >> rfs[] >>
   `ACT_TO_NUM (SND (ptm.prog ' (tm.state,tm.tape_h))) < 4`
     by fs[ACT_TO_NUM_LESS_4] >>
   `(updn [FST (ptm.prog ' (tm.state,tm.tape_h));
           ACT_TO_NUM (SND (p ' (tm.state,tm.tape_h)));
           ⟦tm⟧] =
    ⟦UPDATE_ACT_S_TM (FST (ptm.prog ' (tm.state,tm.tape_h)))
                     (SND (p ' (tm.state,tm.tape_h)))
                     (FULL_DECODE_TM ⟦tm⟧)⟧)`
      by fs[UPDATE_TM_NUM_corol] >>
   simp[pairTheory.UNCURRY] >> fs[Abbr`ptm`] >>
   simp[ENCODED_DECODED_ENCODED_UPDATE_TM_thm,lemma_11]
QED

Theorem CELL_NUM_NUM_CELL[simp]:
  CELL_NUM (NUM_CELL x) = x
Proof
Cases_on `x` >> fs[CELL_NUM_def]
QED

Theorem CELL_NUM_NUM_CELL_RW:
  (NUM_CELL (CELL_NUM c) = c) ==> (NUM_CELL h <> c) ==> (h <> CELL_NUM c)
Proof
  strip_tac >> strip_tac >> metis_tac[]
QED

Theorem NUM_STATE_CELL_NUM_LEM:
  (NUM_CELL (CELL_NUM c) = c) ⇒ ((tm.state = n) ⇒ NUM_CELL tm.tape_h ≠ c) ⇒
   (tm.state = n) ⇒ tm.tape_h ≠ CELL_NUM c
Proof
  strip_tac >> strip_tac >> strip_tac >>
  fs[CELL_NUM_NUM_CELL_RW]
QED

Theorem EQ_SND_P_LESS:
  a <> b  ==> ((p \\ a) ' b  =  p ' b)
Proof
  simp[DOMSUB_FAPPLY_THM]
QED

Theorem UPDATE_W_PROG_NIN_TM:
  ((NUM_CELL (CELL_NUM c) = c) ∧ ((n,CELL_NUM c) ∈ FDOM p) ∧
   n <> 0 ∧ ((tm.state = n) ⇒ NUM_CELL tm.tape_h ≠ c))
  ⇒
  (⟦UPDATE_TAPE (tm with prog := p \\ (n,CELL_NUM c)) ⟧ =
   ⟦UPDATE_TAPE (tm with prog := p)⟧)
Proof
  simp[FULL_ENCODE_TM_def]  >> rw[] >>
  `(tm.state = n) ⇒ tm.tape_h ≠ CELL_NUM c`
    by metis_tac[NUM_STATE_CELL_NUM_LEM] >>
  `(tm.state,tm.tape_h) <> (n,CELL_NUM c)`
    by (simp[] >> metis_tac[]) >>
  rw[] >>
  Cases_on `(tm.state,tm.tape_h) ∈ FDOM p` >>
  rw[UPDATE_TAPE_def] >> fs[EQ_SND_P_LESS] >>
  Cases_on `SND (p ' (tm.state,tm.tape_h))` >> fs[] >>
  Cases_on `tm.tape_l = []` >> fs[] >>
  Cases_on `tm.tape_r = []` >> fs[ENCODE_TM_TAPE_def]
QED

Theorem tm_eq_tm_with_state:
  (tm.state = a) ==> (tm = tm with state := a)
Proof
  strip_tac >> `(tm with state := a).state = a` by fs[] >>
  rfs[TM_component_equality]
QED

Definition effempty_def:
  effempty p <=> FDOM p ⊆ {(a,b) | (a,b) | a = 0}
End

Theorem containment_lem_nzero:
  ((OLEAST n. (nfst n,CELL_NUM (nsnd n)) ∈ FDOM p ∧ nfst n <>0) = NONE)
    ⇔
  effempty p
Proof
  rw[effempty_def] >> eq_tac >> simp[] >> csimp[fmap_EXT] >>
  simp[pairTheory.FORALL_PROD] >> strip_tac
  >- (rw[SUBSET_DEF] >> rename[`sc ∈ FDOM p`] >>
      `∃s c. sc = (s,c)` by simp[pairTheory.pair_CASES]>>
      rw[] >> first_x_assum (qspec_then `s *, (NUM_CELL c)` mp_tac) >>simp[])
  >- (rpt strip_tac >> fs[SUBSET_DEF] >> res_tac >> fs[])
QED

Theorem effempty_no_update:
  effempty tm.prog ==> (UPDATE_TAPE tm = tm with state := 0)
Proof
  rw[effempty_def]>> simp[UPDATE_TAPE_def]>>
  Cases_on `(tm.state,tm.tape_h) ∈ FDOM tm.prog`>> simp[]>>
  fs[SUBSET_DEF] >> res_tac >> fs[]
QED

Theorem CELL_NUM_LEM1:
  (∀n'. n' < n ⊗ c ⇒ nfst n' ≠ 0 ⇒
    (nfst n',CELL_NUM (nsnd n')) ∉ FDOM p) ∧
  (n,CELL_NUM c) ∈ FDOM p ∧ n<>0
     ==>
  (c=0) ∨ (c=1)
Proof
  spose_not_then strip_assume_tac >> Cases_on `CELL_NUM c`
  >- (`0<c` by simp[] >>
      metis_tac[nfst_npair,nsnd_npair,npair2_lt,CELL_NUM_def])
  >- (`1<c` by simp[] >>
      metis_tac[nfst_npair,nsnd_npair,npair2_lt,CELL_NUM_def])
QED

Triviality FULL_ENCODE_IGNORES_PROGS' =
    FULL_ENCODE_IGNORES_PROGS |> SYM  |> Q.INST[`p`|->`ARB` ]

Theorem tmstepf_update_equiv:
  ∀p n tm.
    (n = ⟦tm⟧) ==>
    (tmstepf p n = FULL_ENCODE_TM (UPDATE_TAPE (tm with prog := p) ))
Proof
  ho_match_mp_tac (theorem"tmstepf_ind") >> simp[OLEAST_EQ_SOME] >> rw[] >>
  pop_assum (assume_tac o CONV_RULE (HO_REWR_CONV npair_lem)) >> fs[] >>
  simp[Once tmstepf_def] >>
  Cases_on `
    OLEAST n. (nfst n,CELL_NUM (nsnd n)) ∈ FDOM p ∧ nfst n ≠ 0
  `
  >- (simp[] >> fs[containment_lem_nzero,effempty_no_update] >>
      simp[UPDATE_TAPE_def,FULL_ENCODE_TM_def, ENCODE_TM_TAPE_def]) >>
  fs[OLEAST_EQ_SOME] >> rename [`nfst nc ≠ 0`] >> simp[] >>
  `∃n c. nc = n *, c` by metis_tac[npair_cases] >>
  fs[UPDATE_TAPE_ACT_STATE_TM_thm,NUM_TO_CELL_TO_NUM,
     FULL_ENCODE_TM_STATE] >>
  `NUM_CELL (CELL_NUM c) = c`
    by metis_tac[CELL_NUM_LEM1,NUM_TO_CELL_TO_NUM] >> simp[] >> fs[] >>
  rfs[NUM_CELL_INJ] >>
  Cases_on `(tm.state = n) ∧ (NUM_CELL tm.tape_h = c)` >> rw[]
  >- (fs[updn_UPDATE_TAPE]) >>
  `∃ a s. p ' (n,CELL_NUM c) = (s,a)` by metis_tac[pairTheory.pair_CASES] >>
  first_x_assum(qspecl_then[`n`,`c`,`s`,`a`] mp_tac) >> simp[] >>
  rw[CELL_NUM_NUM_CELL_RW] >> simp[UPDATE_TAPE_def] >>
  Cases_on `(tm.state,tm.tape_h) ∈ FDOM p` >> simp[]
  >- (Cases_on `tm.state = 0` >>simp[]
      >- simp_tac bool_ss [FULL_ENCODE_IGNORES_PROGS, GSYM TM_fupdcanon] >>
      reverse COND_CASES_TAC >- fs[] >>
      simp[DOMSUB_FAPPLY_THM ] >>
      `¬((n = tm.state) ∧ (CELL_NUM c = tm.tape_h))`
         by fs[CELL_NUM_def,NUM_CELL_def] >> simp[] >>
      Cases_on `SND (p ' (tm.state,tm.tape_h))` >> rw[] >>
      ONCE_REWRITE_TAC [FULL_ENCODE_IGNORES_PROGS'] >>
      CONV_TAC (BINOP_CONV (RAND_CONV (SIMP_CONV (srw_ss()) []))) >>
      simp[]) >>
   ONCE_REWRITE_TAC [FULL_ENCODE_IGNORES_PROGS'] >>
   CONV_TAC (BINOP_CONV (RAND_CONV (SIMP_CONV (srw_ss()) []))) >>
   simp[]
QED

Theorem primrec_tmstepf_form:
  ∀n.
    (Cn (proj 0) [
        pr_cond (Cn (pr2 $* ) [Cn pr_eq [Cn (pr1 nfst) [proj 0] ;
                                         Cn (pr1 nfst) [K k] ];
                               Cn pr_eq [Cn pr_mod [
                                            Cn (pr1 nsnd) [
                                              Cn (pr1 nsnd) [proj 0]
                                            ];
                                            twof
                                         ];
                                         Cn (pr1 nsnd) [K k] ] ] )
                (Cn updn [K snum; K anum ; proj 0] )
                (Cn (pr1 (tmstepf q)) [proj 0] )
    ]) [n]
   =
    (λtmn. if (nfst tmn = nfst k) ∧ (nsnd (nsnd tmn) MOD 2 = nsnd k) then
             updn [snum; anum; tmn]
           else tmstepf q tmn) n
Proof
  rw[Cn_def,FUN_EQ_THM] >> rw[pr_cond_def]
QED


Theorem primrec_of_tmstepf:
   primrec (pr1 (tmstepf q)) 1 ==>
   primrec (Cn (proj 0)  [
     pr_cond (Cn (pr2 $* ) [
                     Cn pr_eq [Cn (pr1 nfst) [proj 0] ; Cn (pr1 nfst) [K k] ];
                     Cn pr_eq [
                       Cn pr_mod [Cn (pr1 nsnd) [Cn (pr1 nsnd) [proj 0]] ;twof];
                       Cn (pr1 nsnd) [K k] ] ] )
             (Cn updn [K snum; K anum ; proj 0] )
             (Cn (pr1 (tmstepf q)) [proj 0]  )
   ]) 1
Proof
  strip_tac >> SRW_TAC [][primrec_rules] >> SRW_TAC [][pr_cond_def] >>
  rpt (MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >>
  fs[UPDATE_TM_NUM_PRIMREC]
QED

Theorem primrec_tmstepf:
  primrec (pr1 (tmstepf p)) 1
Proof
  Induct_on `CARD (FDOM p)`
  >- (rpt strip_tac >>
      `FDOM p = {}` by metis_tac[FDOM_FINITE,CARD_EQ_0] >> fs[FDOM_EQ_EMPTY] >>
      rw[Once tmstepf_def] >> qmatch_abbrev_tac`primrec f 1` >>
      `f = Cn (pr2 npair) [zerof; Cn (pr1 nsnd) [proj 0]]` suffices_by
      simp[primrec_rules,primrec_npair,primrec_nsnd] >>
      simp[Abbr`f`,FUN_EQ_THM] >> Cases >>
      simp[proj_def,nsnd_def] >> rw[Once tmstepf_def] >> simp[nsnd_def]  )
  >- (rpt strip_tac >>  MATCH_MP_TAC primrec_pr1  >> rw[Once tmstepf_def] >>
      `(OLEAST n. (nfst n,CELL_NUM (nsnd n)) ∈ FDOM p) <> NONE`
        by (simp[] >> `FDOM p <> {}` by (strip_tac >> fs[]) >>
            `∃a b. (a,b) IN FDOM p`
              by metis_tac[SET_CASES,pairTheory.pair_CASES,IN_INSERT] >>
            qexists_tac`a *, NUM_CELL b` >> simp[]) >>
      Cases_on `
        (OLEAST n. (nfst n,CELL_NUM (nsnd n)) ∈ FDOM p ∧ nfst n ≠ 0)` >>
      fs[]
      >- (qexists_tac `Cn (pr2 npair) [zerof; Cn (pr1 nsnd) [proj 0]]` >>
          conj_tac
          >- simp[primrec_rules,primrec_npair,primrec_nsnd]
          >- simp[proj_def,nsnd_def]) >>
      fs[OLEAST_EQ_SOME] >> rename [‘nfst k <> 0’] >>
      `∃ s a. (p ' (nfst k,CELL_NUM (nsnd k))) = (s,a)`
        by metis_tac[pairTheory.pair_CASES] >> simp[] >>
      `CARD (FDOM (p \\ (nfst k,CELL_NUM (nsnd k)))) = v` by fs[] >>
      qabbrev_tac`q = p \\ (nfst k,CELL_NUM (nsnd k))` >>
      `primrec (pr1 (tmstepf q)) 1` by fs[] >>
      `NUM_CELL (CELL_NUM (nsnd k)) = nsnd k`
        by metis_tac[npair_11,npair,CELL_NUM_LEM1,NUM_TO_CELL_TO_NUM] >>
      fs[] >>
      qabbrev_tac`anum = ACT_TO_NUM a` >>
      qexists_tac`
        Cn (proj 0)  [
          pr_cond
            (Cn (pr2 $* ) [
                Cn pr_eq [Cn (pr1 nfst) [proj 0] ; Cn (pr1 nfst) [K k] ];
                Cn pr_eq [Cn pr_mod [Cn (pr1 nsnd) [Cn (pr1 nsnd) [proj 0]];
                                     twof];
                          Cn (pr1 nsnd) [K k]]
            ])
            (Cn updn [K s; K anum ; proj 0] )
            (Cn (pr1 (tmstepf q)) [proj 0]  )
       ]` >> fs[primrec_of_tmstepf,primrec_tmstepf_form])
QED

Definition tm_return_def:
  tm_return tm =
    if tm.tape_h = Z then 0
    else
      case tm.tape_r of
          [] => 0
        | h::t  => 1 + tm_return (tm with <| tape_h := h;tape_r:=t|>)
Termination
  WF_REL_TAC`measure (LENGTH o (λtm. tm.tape_r))` >> simp[]
End

Definition tm_fn_def:
  tm_fn p args =
    let tm0 = INITIAL_TM p args
    in
      OPTION_MAP (λk. (RUN k tm0)) (OLEAST n. HALTED (RUN n tm0))
End

val _ = temp_overload_on ("un_nlist", “listOfN”)

Definition INITIAL_TM_NUM_def:
  INITIAL_TM_NUM = (λl. ⟦INITIAL_TM FEMPTY (un_nlist (proj 0 l))⟧)
End

Definition RUN_NUM_def:
  RUN_NUM p targs = Pr (INITIAL_TM_NUM) (Cn (pr1 (tmstepf p)) [proj 1]) targs
End

Theorem INITIAL_TAPE_PROG:
  (INITIAL_TAPE_TM tm l) with prog := p = INITIAL_TAPE_TM (tm with prog := p) l
Proof
Cases_on `l` >> simp[INITIAL_TAPE_TM_def]
QED

Theorem UPDATE_TAPE_PROG:
  (tm.prog = p) ==> ((UPDATE_TAPE tm) with prog := p = UPDATE_TAPE tm)
Proof
strip_tac >>simp[UPDATE_TAPE_def] >> rw[] >>
Cases_on `SND (tm.prog ' (tm.state,tm.tape_h))` >>simp[TM_component_equality]
QED

Theorem UPDATE_PROG_CONSERVE[simp]:
  (UPDATE_TAPE tm).prog = tm.prog
Proof
simp[UPDATE_TAPE_def] >> rw[] >>
Cases_on `SND (tm.prog ' (tm.state,tm.tape_h))` >>simp[TM_component_equality]
QED

Theorem RUN_PROG_CONSERVE[simp]:
  (RUN n tm).prog = tm.prog
Proof
Induct_on `n` >> simp[FUNPOW_SUC]
QED

Theorem RUN_PROG:
  (tm.prog = p) ==> ((RUN n tm) with prog := p = RUN n tm)
Proof
 simp[TM_component_equality]
QED

Theorem INITIAL_TAPE_TM_PROG[simp]:
  (INITIAL_TAPE_TM tm args).prog = tm.prog
Proof
Cases_on `args` >> simp[INITIAL_TAPE_TM_def]
QED

Theorem INITIAL_TM_PROG[simp]:
  (INITIAL_TM p args).prog = p
Proof
 simp[INITIAL_TM_def]
QED

Theorem RUN_NUM_corr:
  RUN_NUM p [t;args] = ⟦FUNPOW UPDATE_TAPE t (INITIAL_TM p (un_nlist args))⟧
Proof
  simp[RUN_NUM_def] >> Induct_on `t` >> fs[]
  >- (simp[INITIAL_TM_NUM_def,INITIAL_TM_def] >>
      ONCE_REWRITE_TAC[FULL_ENCODE_IGNORES_PROGS
                         |> Q.INST [`p`|-> `ARB` ] |> SYM] >>
      simp_tac bool_ss[INITIAL_TAPE_PROG] >>simp[])
  >- (simp[FUNPOW_SUC] >> rw[SIMP_RULE bool_ss[] tmstepf_update_equiv] >>
      fs[RUN_PROG])
QED

Definition tm_return_num_def:
  tm_return_num =
    Pr (Cn (pr1 nsnd) [Cn (pr1 nsnd) [proj 0]])
       (pr_cond (Cn pr_eq [Cn pr_mod [Cn pr_div [proj 2;proj 0]; twof]; zerof])
                (proj 1)
                (Cn (pr2 $+) [proj 1;onef]))
End

val _ = temp_set_fixity "*." (Infixl 600)
val _ = temp_overload_on ("*.", ``λn m. Cn (pr2 $*) [n; m]``)


Definition pr_exp_def:
  pr_exp = Cn (Pr onef ( proj 1 *. ( proj 2))) [proj 1;proj 0]
End

Theorem primrec_pr_exp[simp]:
  primrec pr_exp 2
Proof
 rw[pr_exp_def] >> SRW_TAC [][primrec_rules] >> SRW_TAC [][pr_cond_def] >>
  rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules])
QED


Definition tm_log_num_def:
  tm_log_num =
    minimise (SOME ∘
              Cn pr_eq [
                 Cn pr_mod [
                   Cn pr_div [proj 1; Cn pr_exp [twof;Cn succ [proj 0] ] ];
                   twof
                 ];
                 zerof
               ])
End

Theorem primrec_tm_log_num:
  primrec (Cn pr_eq [Cn pr_mod [Cn pr_div [proj 1;
                                           Cn pr_exp [twof;Cn succ [proj 0]]];
                                twof];
                     zerof ]) 2
Proof
  SRW_TAC [][primrec_rules] >> SRW_TAC [][pr_cond_def] >>
  rpt (MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >>
  simp[primrec_pr_exp]
QED

val recfn_rulesl = CONJUNCTS recfn_rules
Theorem recfnMin = List.nth(recfn_rulesl, 5)

Theorem recfn_tm_log_num:
  recfn tm_log_num 1
Proof
  `recfn (SOME o
          Cn pr_eq [Cn pr_mod [Cn pr_div [proj 1;
                                          Cn pr_exp [twof;Cn succ [proj 0]]];
                               twof] ;
                    zerof]) 2`
     by simp[primrec_recfn,primrec_tm_log_num] >>
  rw[tm_log_num_def] >> rfs[recfnMin]
QED

Theorem primrec_tm_ret_run:
  primrec tm_return_num 2
Proof
  `primrec (Cn (pr1 nsnd) [Cn (pr1 nsnd) [proj 0]]) 1`
     by (SRW_TAC [][primrec_rules] >>
         SRW_TAC [][pr_cond_def] >>
         rpt (MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules])) >>
  `primrec (pr_cond (Cn pr_eq [Cn pr_mod [Cn pr_div [proj 2;proj 0]; twof];
                               zerof])
                    (proj 1)
                    (Cn (pr2 $+) [proj 1;onef] )) 3`
     by (SRW_TAC [][primrec_rules] >>
         SRW_TAC [][pr_cond_def] >>
         rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]))  >>
  rw[tm_return_num_def,primrec_pr]
QED


Theorem INITIAL_TAPE_PRES_STATE[simp]:
  (INITIAL_TAPE_TM tm k).state = tm.state
Proof
  Cases_on `k` >> rw[INITIAL_TAPE_TM_def]
QED

Definition pr_neq_def:
  pr_neq = Cn (pr2 $+) [Cn (pr2 $-) [pr_le; cflip pr_le];
                        Cn (pr2 $-) [cflip pr_le; pr_le]]
End

Theorem pr_neq_thm:
  pr_neq [n;  m] = nB (n <> m)
Proof
  SRW_TAC [ARITH_ss][pr_neq_def] >> Cases_on `n<=m` >> Cases_on `m<=n` >> fs[]
QED

Theorem primrec_pr_neq[simp]:
  primrec pr_neq 2
Proof
SRW_TAC [][pr_neq_def, primrec_rules]
QED

Definition el_zero_def:
  (el_zero 0 = 1) ∧
  (el_zero (SUC n) =
    let t = ntl (SUC n)
    in
      napp (el_zero n) (ncons (nel t (el_zero n) + 1) 0))
End

Theorem ntl_nlist_unnlist:
  ntl (SUC n) = nlist_of (TL (un_nlist (SUC n)))
Proof
  ‘∀n. 0 < n ⇒ ntl n = nlist_of (TL (listOfN n))’ suffices_by simp[] >>
  ho_match_mp_tac nlist_ind >> simp[]
QED

Theorem length_unnlist:
  0 < LENGTH (un_nlist (SUC n))
Proof
fs[DECIDE “0 < n ⇔ n ≠ 0”]
QED

Theorem ntl_suc_less:
  ∀n. ntl (SUC n) <= n
Proof
strip_tac >> rw[ntl_def,nsnd_le]
QED

Theorem nel_nlist_of:
  i < nlen l ⇒ nel i l = EL i (listOfN l)
Proof
  simp[GSYM nel_correct]
QED

Theorem el_zero_corr:
  el_zero n = nlist_of (GENLIST (LENGTH o un_nlist) (n+1))
Proof
  Induct_on `n` >> fs[el_zero_def] >- EVAL_TAC >>
  `ntl (SUC n) <= n` by simp[ntl_suc_less] >>
  simp[ADD_CLAUSES,GENLIST,SNOC_APPEND,nel_nlist_of] >>
  qspec_then ‘n + 1’ strip_assume_tac nlist_cases >> fs[ADD1]
QED

Definition nleng_def:
  nleng n = nel n (el_zero n)
End

(*  add_persistent_funs ["numpair.nlistrec_def"] *)

Theorem nlen_reduc:
  ∀n. nlen (SUC n) = nlen (ntl (SUC n)) + 1
Proof
  strip_tac >> `SUC n <> 0` by fs[] >>
  `∃h t. SUC n = ncons h t ` by metis_tac[nlist_cases] >> rw[]
QED

Definition pr_el_zero_def:
  pr_el_zero =
    Cn (Pr (onef)
           (Cn (pr2 napp) [ proj 1 ;
                            Cn (pr2 ncons) [
                              Cn succ [
                                Cn (pr2 nel) [
                                  Cn (pr1 ntl) [
                                    Cn succ [proj 0]
                                  ];
                                  proj 1
                                ]
                              ];
                              zerof
                            ]
                          ]))
       [proj 0;onef]
End

Theorem primrec_pr_el_zero:
  primrec pr_el_zero 1
Proof
  fs[pr_el_zero_def] >> rpt (irule primrec_cn >> rw[primrec_rules]) >>
  irule alt_Pr_rule >>
  fs[primrec_rules] >> rpt (irule primrec_cn >> rw[primrec_rules])
QED

Theorem primrec_el_zero:
  primrec (pr1 el_zero) 1
Proof
`(∃g. primrec g 1 ∧ ∀n. g [n] = el_zero n)` suffices_by fs[primrec_pr1] >>
 qexists_tac `pr_el_zero` >> fs[primrec_pr_el_zero] >> strip_tac >> Induct_on `n` >- EVAL_TAC >>
 rw[el_zero_def,pr_el_zero_def] >> `Pr onef (Cn (pr2 napp) [proj 1;
 Cn (pr2 ncons) [Cn succ [Cn (pr2 nel) [Cn (pr1 ntl) [Cn succ [proj 0]]; proj 1]]; zerof]]) [n; 1]= pr_el_zero [n]` by
 fs[pr_el_zero_def] >> rfs[] >> rw[] >> fs[ADD1]
QED

Theorem primrec_nleng:
  primrec (pr1 nleng) 1
Proof
`(∃g. primrec g 1 ∧ ∀n. g [n] = nleng n)` suffices_by fs[primrec_pr1] >>
 qexists_tac`Cn (pr2 nel) [proj 0;Cn (pr1 el_zero) [proj 0]]` >> conj_tac
 >- (rpt (irule primrec_cn >> rw[primrec_rules]) >> fs[primrec_el_zero])
 >- (strip_tac >> fs[nleng_def]  )
QED

Triviality Pr_eval:
  0 < m ==> (Pr b r (m :: t) = r (m - 1 :: Pr b r (m - 1 :: t) :: t))
Proof
STRIP_TAC THEN SIMP_TAC (srw_ss()) [Once Pr_def, SimpLHS] THEN
          Cases_on `m` THEN SRW_TAC [ARITH_ss][]
QED


(* Pr defs, probs use *)
Definition pr_log_def:
pr_log = Cn (pr2 $- ) [Cn (Pr (zerof) (Cn (pr2 $+) [proj 1; Cn pr_neq [zerof;Cn pr_div [Cn (pr1 nfst) [proj 2];
         Cn pr_exp [Cn (pr1 nsnd) [proj 2];proj 0 ]]]]))
            [proj 0;Cn (pr2 npair) [proj 0;proj 1]];onef]
End

Definition pr_tl_en_con_fun2_def:
pr_tl_en_con_fun2 =
               Cn (pr2 $+) [Cn (pr2 $* )
  [Cn (pr2 $-) [ Cn pr_exp [twof;Cn (pr2 nel)
  [proj 0;proj 2 ]];onef ];
      Cn pr_exp [twof;Cn pr_log [proj 1;twof] ] ];
                                proj 1]
End

Definition order_flip_def:
order_flip = Cn (Pr (zerof )
                (Cn (pr2 ncons) [Cn (pr2 nel) [proj 0;proj 2] ;proj 1] ))
                [Cn (pr1 nleng) [proj 0];proj 0]
End

Definition pr_tl_en_con_fun4_def:
pr_tl_en_con_fun4 = Cn (pr2 $+) [Cn (pr2 $-)
                   [Cn pr_exp [twof;Cn (pr2 nel) [proj 0;Cn order_flip [proj 2] ]];onef ];
                    Cn (pr2 $* ) [proj 1;Cn pr_exp [twof;Cn succ
   [ Cn pr_log [Cn pr_exp [twof;Cn (pr2 nel) [proj 0;Cn order_flip [proj 2]]] ; twof]] ]]]
End

Definition pr_tl_en_con_def:
pr_tl_en_con = Cn (pr1 DIV2) [Cn (Pr (zerof) (pr_tl_en_con_fun4)) [Cn (pr1 nleng) [proj 0];proj 0]]
End

Theorem primrec_order_flip:
  primrec order_flip 1
Proof
rw[order_flip_def] >> rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >>fs[primrec_nleng]
QED

Theorem primrec_pr_log:
  primrec pr_log 2
Proof
rw[pr_log_def] >> rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> irule alt_Pr_rule >> rw[primrec_rules] >> rpt (irule primrec_cn >> rw[primrec_rules])
QED


Theorem primrec_pr_tl_en_con_fun4:
  primrec pr_tl_en_con_fun4 3
Proof
rw[pr_tl_en_con_fun4_def] >> rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules]) >> rw[primrec_rules,primrec_pr_exp,primrec_order_flip,primrec_pr_log] >> fs[primrec_nleng]
QED

Theorem primrec_pr_tl_en_con:
  primrec pr_tl_en_con 1
Proof
SRW_TAC [][pr_tl_en_con_def,primrec_rules] >>
        rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules,primrec_div2,primrec_nleng]) >>
        fs[primrec_nleng] >>  irule alt_Pr_rule >> rw[primrec_pr_tl_en_con_fun4]
QED


Theorem invtri_zero[simp]:
  invtri 0 = 0
Proof
EVAL_TAC
QED

Theorem ntl_zero[simp]:
  ntl 0 = 0
Proof
EVAL_TAC
QED

Theorem invtri_nzero[simp]:
  (invtri n = 0) <=> (n = 0)
Proof
eq_tac >> fs[] >>
       SRW_TAC [][invtri_def] >>
       Q.SPECL_THEN [`n`,`0`] MP_TAC invtri0_thm >>
       SRW_TAC [ARITH_ss][tri_def] >> `n < SUC 0` by metis_tac[SND_invtri0] >> rw[]
QED

Theorem nsnd_fun_thm[simp]:
 (nsnd n = n) <=>  (n = 0)
Proof
eq_tac >> rw[nsnd_def]  >> Cases_on `n` >> fs[] >>
`tri (invtri (SUC n')) = 0` by  fs[SUB_EQ_EQ_0] >> `tri 0 = 0` by fs[tri_def] >>
`invtri (SUC n') = 0` by rfs[tri_11]  >>  fs[]
QED

Theorem nsnd_lthen[simp]:
  ∀n. (nsnd n < n)<=> (n<> 0)
Proof
strip_tac >> eq_tac >> fs[] >> strip_tac >> `nsnd n <= n` by fs[nsnd_le] >> `nsnd n <> n` by fs[] >> rw[]
QED

Theorem FUNPOW_mono:
  (∀n m. m <= n ==> f m <= f n) ==> (∀n m k. m <= n ==> FUNPOW f k m <= FUNPOW f k n)
Proof
rpt strip_tac >> Induct_on `k` >> fs[] >> fs[FUNPOW_SUC]
QED

Theorem ENCODE_TL_DIV2:
  ENCODE (TL (h::t)) = DIV2 (ENCODE (h::t))
Proof
Cases_on `h` >> fs[ENCODE_def,DIV2_def,TWO_TIMES_DIV_TWO_thm]
QED

Theorem el_zero_exp:
  el_zero n = nlist_of ((GENLIST (LENGTH ∘ un_nlist) n) ++ [(LENGTH ∘ un_nlist) n])
Proof
`n+1 = SUC n` by fs[ADD1] >> rw[GENLIST,SNOC_APPEND,el_zero_corr]
QED

Theorem el_zero_napp:
  el_zero n = napp (nlist_of (GENLIST (LENGTH ∘ un_nlist) n)) (nlist_of [(LENGTH ∘ un_nlist) n])
Proof
fs[el_zero_exp]
QED

Definition r_zero_def:
  (r_zero 0 = ncons 0 0) ∧
  (r_zero (SUC n) =
   let t = ntl (SUC n); r0n = r_zero n; revt = nel t r0n;
      res = napp revt (ncons (nhd (SUC n)) 0)
   in
     napp r0n (ncons res 0))
End

Theorem r_zero_corr:
  r_zero n = nlist_of (GENLIST (nlist_of o REVERSE o un_nlist) ( n+1))
Proof
  Induct_on `n` >> fs[r_zero_def,ADD_CLAUSES] >>
  `ntl (SUC n)<= n` by fs[ntl_suc_less]>>
  rw[GENLIST, SNOC_APPEND,nel_nlist_of] >>
  `∃l. n+1 = nlist_of l` by metis_tac[nlist_of_SURJ] >> rw[ADD1] >>
   Cases_on `l` >> fs[]
QED

Overload "order_flip" = ``pr1 (λn. nel n (r_zero n))``

Theorem order_flip_corr:
  order_flip [n] = nlist_of (REVERSE (un_nlist n))
Proof
fs[r_zero_corr,nel_nlist_of]
QED

Theorem order_flip_ncons[simp]:
  order_flip [ncons h t] = napp (order_flip [t]) (ncons h 0)
Proof
  fs[order_flip_corr]
QED

Definition list_rec_comb_def:
  list_rec_comb c n 0 = ncons n 0  ∧
  list_rec_comb c n (SUC k) =
    let t = ntl (SUC k); h=nhd (SUC k); rl = list_rec_comb c n k;
        r = nel t rl
    in napp rl (ncons (c [h; t; r]) 0)
End

Definition LIST_REC_def:
  (LIST_REC c (n:num) [] = n) ∧
  (LIST_REC c n (h::t) = c [h;nlist_of t;LIST_REC c n t])
End

Theorem list_rec_comb_corr:
  list_rec_comb c n k = nlist_of (GENLIST (LIST_REC c n o un_nlist) (k+1))
Proof
  Induct_on `k` >> fs[list_rec_comb_def,LIST_REC_def,ADD_CLAUSES]>>
  `ntl (SUC k)<= k` by fs[ntl_suc_less]>>
  rw[GENLIST, SNOC_APPEND,nel_nlist_of] >> rw[] >> rw[ADD1] >>
  `∃l. k+1 = nlist_of l` by metis_tac[nlist_of_SURJ]>> rw[] >>
  Cases_on `l` >> fs[] >> rw[LIST_REC_def]
QED

Theorem primrec_list_rec_comb:
  primrec c 3 ==> primrec (pr1 (list_rec_comb c n)) 1
Proof
  strip_tac >> irule primrec_pr1 >>
  qexists_tac`
    Pr1 (ncons n 0) (
      Cn (pr2 napp) [
        proj 1;
        Cn (pr2 ncons) [
          Cn c [
            Cn (pr1 nhd) [Cn succ [proj 0]];
            Cn (pr1 ntl) [Cn succ [proj 0]];
            Cn (pr2 nel) [Cn (pr1 ntl) [Cn succ [proj 0]];proj 1 ]
          ];
          zerof
        ]
      ]
    )
  ` >> conj_tac
  >- (irule primrec_Pr1 >>
      rpt (irule primrec_cn >> rw[primrec_rules,primrec_napp,primrec_ncons])) >>
  Induct >> fs[list_rec_comb_def]
QED

Theorem list_num_rec_thm:
  ∀n c.(primrec c 3)==> ∃f.(primrec f 1) ∧ (f [0] = n) ∧ (∀h t. f [ncons h t] = c [h; t; (f [t])])
Proof
rpt strip_tac >> qexists_tac`Cn (pr2 nel) [proj 0;Cn (pr1 (list_rec_comb c n)) [proj 0]] ` >>
rpt conj_tac >- (rpt (irule primrec_cn >> rw[primrec_rules,primrec_nel,primrec_list_rec_comb]))>>
 simp[list_rec_comb_def] >> simp[list_rec_comb_corr,nel_nlist_of,LIST_REC_def]
QED

val nrev_thm = new_specification("nrev_def", ["nrev"],
list_num_rec_thm |> SPECL[``0n``,``Cn (pr2 napp) [proj 2;Cn (pr2 ncons) [proj 0;zerof] ]``]
                 |> SIMP_RULE (srw_ss())[primrec_cn, primrec_rules])

val concatWith_Z_thm = new_specification("concatWith_Z_def", ["concatWith_Z"],
 list_num_rec_thm |> SPECL[``0n``,``pr_cond (Cn pr_eq [proj 1;zerof])
 (proj 0) (Cn (pr2 napp) [proj 0; Cn (pr2 napp) [onef;proj 2]])``]
                 |> SIMP_RULE (srw_ss())[primrec_cn, primrec_rules])

Theorem concatWith_Z_corr:
  concatWith_Z [x] = nlist_of (concatWith [0] (MAP un_nlist (un_nlist x)))
Proof
  completeInduct_on `x` >>
  `(x = 0) ∨ ∃h t. x = ncons h t` by metis_tac[nlist_cases] >>
  simp[concatWith_Z_thm,concatWith_def] >> rw[] >>
  simp[concatWith_Z_thm,concatWith_def] >>
  `t < ncons h t`
     by (simp[ncons_def] >>
         `t = nsnd (h *, t)` by simp[] >>
         `nsnd (h *, t) <= h *, t` by simp[nsnd_le] >> simp[] ) >>
  RES_TAC >> simp[concatWith_def] >>
  `∃h' t'. t = ncons h' t'` by metis_tac[nlist_cases] >>
  simp[concatWith_def] >>
  ‘ncons 0 0 = 1’ suffices_by (disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  EVAL_TAC
QED

Theorem INITIAL_TAPE_PRES_L[simp]:
  (INITIAL_TAPE_TM tm (h::t)).tape_l = []
Proof
fs[INITIAL_TAPE_TM_def]
QED

Definition tape_encode_def:
  tape_encode = pr_cond (Cn pr_eq [proj 1;zerof])
   (Cn (pr2 npair) [proj 0;Cn (pr2 $*) [twof;proj 2]])
  (Cn (pr2 npair) [proj 0;Cn succ [Cn (pr2 $* ) [twof;proj 2]]])
End

Theorem primrec_tape_encode[simp]:
  primrec tape_encode 3
Proof
fs[tape_encode_def] >> irule primrec_pr_cond >> rpt conj_tac >>
rpt (irule primrec_cn >>
     rw[primrec_rules,primrec_pr_cond,primrec_pr_eq,primrec_pr_mult])
QED

Theorem tape_encode_corr:
  tape_encode [ENCODE tm.tape_l;NUM_CELL tm.tape_h;ENCODE tm.tape_r] = ENCODE_TM_TAPE tm
Proof
fs[tape_encode_def,ENCODE_TM_TAPE_def] >> `CELL_NUM (NUM_CELL tm.tape_h) = tm.tape_h` by
 fs[CELL_NUM_NUM_CELL]>> `CELL_NUM 0 = Z` by fs[CELL_NUM_def]>>`NUM_CELL Z = 0` by fs[NUM_CELL_def]
>>`(NUM_CELL tm.tape_h = 0) ⇔ (tm.tape_h = Z)` by metis_tac[NUM_CELL_INJ] >>rw[]
QED

Theorem tape_encode_corr_sym:
  ENCODE_TM_TAPE tm = tape_encode [ENCODE tm.tape_l;NUM_CELL tm.tape_h;ENCODE tm.tape_r]
Proof
fs[tape_encode_corr]
QED


(* Define correctly so it matches what it should *)
Definition pr_INITIAL_TAPE_TM_NUM_def:
pr_INITIAL_TAPE_TM_NUM = pr_cond (Cn pr_eq [proj 1;zerof]) (proj 0) (Cn (pr2 npair)
[Cn (pr1 nfst) [proj 0];Cn (pr2 npair) [Cn (pr1 nhd) [proj 1];Cn (pr1 ntl) [proj 1]] ])
End

Theorem primrec_pr_INITIAL_TAPE_TM_NUM[simp]:
  primrec pr_INITIAL_TAPE_TM_NUM 2
Proof
  fs[pr_INITIAL_TAPE_TM_NUM_def] >> `0<2` by fs[] >>
  irule primrec_pr_cond >> rpt conj_tac >>
  rpt (irule primrec_cn >>
       rw[primrec_rules,primrec_pr_eq,primrec_nsnd,primrec_nfst]) >>
  fs[primrec_proj]
QED

Definition pr_ODD_def:
  pr_ODD = pr_cond (Cn pr_eq [Cn pr_mod [proj 0;twof];onef]) onef zerof
End

Theorem pr_ODD_corr:
  pr_ODD [x] = if ODD x then 1 else 0
Proof
fs[pr_ODD_def] >> Cases_on `ODD x` >- metis_tac[ODD_MOD_TWO_lem] >>
`EVEN x` by metis_tac[EVEN_OR_ODD] >> fs[EVEN_MOD2]
QED

Theorem GENLIST_ZERO:
  (GENLIST a b = []) <=> (b=0)
Proof
eq_tac >> fs[GENLIST] >> strip_tac >> Cases_on `b` >> fs[GENLIST]
QED

Theorem concatWith_Z_empty:
  (concatWith [Z] (MAP (GENLIST (K O)) args) = []) <=> ((args = []) ∨ (args = [0]))
Proof
eq_tac >- (strip_tac >> Cases_on `MAP (GENLIST (K O)) args` >> rfs[concatWith_def] >>
      Cases_on `t` >> rfs[concatWith_def] >> `GENLIST (K O) x0 = []` by fs[] >> fs[GENLIST_ZERO])
       >- (strip_tac >> rw[concatWith_def])
QED

Theorem head_concatWith:
  ((l<> []) ∧ (HD l <> [])) ==> (HD (concatWith a l) = HD (HD l))
Proof
strip_tac >> Cases_on `l` >> fs[concatWith_def] >> Cases_on `t` >> fs[concatWith_def,HD] >>
                                 Cases_on `h` >> fs[]
QED

Theorem head_nil_concatWith[simp]:
  HD (concatWith [a] ([]::b::c)) = a
Proof
rw[concatWith_def]
QED

Theorem odd_encode_hd_concat:
  (concatWith [Z] (MAP (GENLIST (K O)) args) <> []) ==> (NUM_CELL (HD (concatWith [Z] (MAP (GENLIST (K O)) args))) = 1 - pr_eq [proj 0 args;0])
Proof
strip_tac >> fs[concatWith_Z_empty]
          >> Cases_on `args` >- rw[concatWith_def] >> Cases_on `h = 0` >> simp[proj_def]>>
          Cases_on `MAP (GENLIST (K O)) t`>> simp[]
          >- (`t = []` by fs[MAP_EQ_NIL] >> rw[]) >> simp[concatWith_def]
          >- (`∃h'. h = SUC h'` by metis_tac[num_CASES] >> rw[] >> fs[HD_GENLIST])
          >- (`∃h'. h = SUC h'` by metis_tac[num_CASES] >> rw[] >> fs[GENLIST_CONS])
QED

Theorem nfst_zero[simp]:
  nfst 0 = 0
Proof
  EVAL_TAC
QED

Theorem nsnd_zero[simp]:
  nsnd 0 = 0
Proof
  EVAL_TAC
QED

Theorem nhd_zero[simp]:
  nhd 0 = 0
Proof
  EVAL_TAC
QED

Theorem nstl_zero[simp]:
  ntl 0 = 0
Proof
  EVAL_TAC
QED

Theorem num_cell_encode_hd_concat:
  (concatWith [Z] (MAP (GENLIST (K O)) args) <> []) ==> (NUM_CELL (HD (concatWith [Z] (MAP (GENLIST (K O)) args))) = 1 - pr_eq [ nhd  (nlist_of args);0])
Proof
rw[odd_encode_hd_concat] >> Cases_on `args` >> simp[nhd_thm]
QED

Definition encode_concat_def:
    (encode_concat 0 = 0) ∧
    (encode_concat args = (2 ** (nhd args) - 1) +
                          (2* (2** (nhd args)) * encode_concat (ntl args)))
Termination
 qexists_tac `$<` >> conj_tac >- simp[prim_recTheory.WF_LESS] >> strip_tac >>
 `ntl (SUC v) <= v` by simp[ntl_suc_less] >>
 `v < SUC v` by simp[prim_recTheory.LESS_SUC_REFL]>> rw[]
End

Definition encode_tl_concat_def:
  encode_tl_concat args = DIV2 (encode_concat args)
End

Theorem ENCODE_GENLIST_p_Z:
  ENCODE (GENLIST (K O) h ++ [Z] ++ b) = ((2**h) - 1) + (2*((2**h))*(ENCODE b))
Proof
Induct_on `h` >> simp[ENCODE_def] >> simp[GENLIST_CONS] >> simp[ENCODE_def] >>rw[EXP] >>
`2 * (2 ** h − 1 + 2 * (ENCODE b * 2 ** h)) = 2*2 ** h − 2*1 + 4 * (ENCODE b * 2 ** h)` by fs[]>>
rw[] >> `2<=2*2**h` by (rpt (pop_assum kall_tac) >> Induct_on `h` >> simp[])  >> simp[]
QED

Theorem ENCODE_GENLIST_O:
  ENCODE (GENLIST (K O) h) = 2 ** h − 1
Proof
  Induct_on `h` >> simp[ENCODE_def,GENLIST_CONS,EXP] >>
  simp[LEFT_SUB_DISTRIB] >>
  `2 <= 2 * 2**h` suffices_by decide_tac >> simp[]
QED

Theorem encode_concat_corr:
  ENCODE (concatWith [Z] (MAP (GENLIST (K O)) args)) = encode_concat (nlist_of args)
Proof
Induct_on `args` >> fs[concatWith_def,ENCODE_def,encode_concat_def] >> strip_tac >>
`nhd (ncons h (nlist_of args)) = h` by simp[nhd_thm] >> `ntl (ncons h (nlist_of args)) =
nlist_of args` by simp[ntl_thm] >> `ncons h (nlist_of args) <> 0` by simp[ncons_not_nnil] >>
`∃ n0. ncons h (nlist_of args) = SUC n0 ` by metis_tac[num_CASES] >>rw[encode_concat_def] >>
full_simp_tac bool_ss[] >>
Cases_on `args` >> simp[concatWith_def] >- simp[encode_concat_def,ENCODE_GENLIST_O] >>
simp[ENCODE_GENLIST_p_Z] >> fs[]
QED

Definition pr_INITIAL_TM_NUM_def:
  pr_INITIAL_TM_NUM = Cn (pr2 npair) [zerof;Cn tape_encode
                                               [zerof;
                                                Cn (pr2 $-) [onef ;Cn pr_eq [Cn (pr1 nhd) [proj 0];zerof]];
                                              Cn (pr1 encode_tl_concat) [proj 0]]]
End

Theorem encode_concat_list_rec:
  encode_concat n =
  nel n (
    list_rec_comb (
      Cn (pr2 $+) [
        Cn (pr1 PRE) [Cn (pr2 $EXP) [twof;proj 0]];
        Cn (pr2 $*) [twof;Cn (pr2 $*) [proj 2;Cn (pr2 $EXP) [twof;proj 0]]]
      ]
    ) 0 n
  )
Proof
  rw[list_rec_comb_corr] >>
  `∃l.  n =  nlist_of l` by metis_tac[nlist_of_SURJ] >> rw[] >>
  Induct_on `l` >> simp[LIST_REC_def,encode_concat_def] >> strip_tac >>
  `ncons h (nlist_of l) <> 0` by simp[ncons_not_nnil] >>
  `∃ n0. ncons h (nlist_of l) = SUC n0 ` by metis_tac[num_CASES] >>
  rw[encode_concat_def] >>
  full_simp_tac bool_ss[] >> pop_assum (SUBST_ALL_TAC o SYM) >>
  simp[nel_nlist_of,LIST_REC_def]
QED

Definition pr_encode_concat_def:
  pr_encode_concat =
  Cn (pr2 nel) [
   proj 0;
   Cn (pr1 (list_rec_comb (Cn (pr2 $+) [
     Cn (pr1 PRE) [Cn (pr2 $EXP) [twof;proj 0]];
     Cn (pr2 $*) [twof;Cn (pr2 $*) [proj 2;Cn (pr2 $EXP) [twof;proj 0]]]
   ]) 0)) [proj 0]
  ]
End

Definition pr_encode_tl_concat_def:
  pr_encode_tl_concat = Cn (pr1 DIV2) [Cn (pr2 nel) [proj 0;
   Cn (pr1 (list_rec_comb (Cn (pr2 $+) [Cn (pr1 PRE) [Cn (pr2 $EXP) [twof;proj 0]];
   Cn (pr2 $*) [twof;Cn (pr2 $*) [proj 2;Cn (pr2 $EXP) [twof;proj 0]]]]) 0)) [proj 0]]]
End

Theorem primrec_exp:
  primrec (pr2 $**) 2
Proof
 irule primrec_pr2 >>qexists_tac `pr_exp` >> conj_tac >-simp[primrec_pr_exp] >> simp[pr_exp_def]>>
Induct >> Induct >> simp[] >> rw[EXP]
QED

Theorem primrec_pr_INITIAL_TM_NUM[simp]:
  primrec pr_INITIAL_TM_NUM 1
Proof
SRW_TAC [][pr_INITIAL_TM_NUM_def,primrec_rules] >>
        rpt ( MATCH_MP_TAC primrec_cn >> SRW_TAC [][primrec_rules,concatWith_Z_thm,primrec_pr_INITIAL_TAPE_TM_NUM,primrec_tape_encode,primrec_npair,primrec_ntl,primrec_nhd]) >>
        irule primrec_pr1 >> qexists_tac `pr_encode_tl_concat` >> conj_tac
        >- (rw[pr_encode_tl_concat_def] >>rpt (irule primrec_cn >> rw[primrec_rules,primrec_nel] )>-
(`primrec (Cn (pr2 $+)
             [Cn (pr1 PRE) [Cn (pr2 $** ) [twof; proj 0]];
              twof *. (proj 2 *. Cn (pr2 $** ) [twof; proj 0])]) 3` suffices_by
        rw[primrec_list_rec_comb] >> rpt (irule primrec_cn >> rw[primrec_rules,primrec_nel] ) >>
        simp[primrec_exp,primrec_div2]) >> simp[primrec_div2] )
        >- (strip_tac >> simp[encode_concat_list_rec] >> `∃l.  n =  nlist_of l` by metis_tac[nlist_of_SURJ] >> rw[] >> Induct_on `l` >> simp[list_rec_comb_def,encode_tl_concat_def,encode_concat_def,nlist_of_def,pr_encode_concat_def] >- simp[pr_encode_concat_def,pr_encode_tl_concat_def,list_rec_comb_def] >> strip_tac >> simp[pr_encode_tl_concat_def,encode_concat_list_rec]   )
QED

Theorem tape_encode_thm:
  tape_encode [a;b;c] = if b=0 then a *, (2* c) else a *, (SUC (2*c))
Proof
fs[tape_encode_def]
QED

Theorem tape_encode_eq:
  (((b=0) ∨ (b=1)) ∧ ((e=0) ∨ (e=1))) ==>
                     ( (tape_encode [a;b;c] = tape_encode [d;e;f]) <=> ((a=d) ∧ (b=e) ∧(c=f)))
Proof
strip_tac >> eq_tac >> rw[tape_encode_thm]
         >- (CCONTR_TAC >> rfs[] >> `ODD (SUC (2* f))` by fs[ODD_DOUBLE] >> `EVEN (2*c)` by
           fs[EVEN_DOUBLE] >> rfs[EVEN_AND_ODD] >> fs[EVEN,EVEN_DOUBLE] )
         >- (CCONTR_TAC >> rfs[] >> `ODD (SUC (2* c))` by fs[ODD_DOUBLE] >> `EVEN (2*f)` by
           fs[EVEN_DOUBLE] >> rfs[EVEN_AND_ODD] >> metis_tac[EVEN_AND_ODD])
QED

Theorem ENCODE_TL_concatWith:
  (concatWith [Z] (MAP (GENLIST (K O)) args) = h::t) ==> (ENCODE t = encode_tl_concat (nlist_of args))
Proof
rw[] >> simp[encode_tl_concat_def] >> `ENCODE t = ENCODE (TL (concatWith [Z] (MAP (GENLIST (K O)) args)))`
by simp[] >> metis_tac[encode_concat_corr,ENCODE_TL_DIV2]
QED

Theorem primrec_INITIAL_TM_NUM:
  primrec INITIAL_TM_NUM 1
Proof
  `INITIAL_TM_NUM = pr_INITIAL_TM_NUM`
    suffices_by fs[primrec_pr_INITIAL_TM_NUM] >>
  fs[FUN_EQ_THM] >> strip_tac >>
  fs[INITIAL_TM_NUM_def,INITIAL_TM_def,INITIAL_TAPE_TM_def,
     FULL_ENCODE_TM_def,pr_INITIAL_TM_NUM_def,tape_encode_corr_sym] >>
  Cases_on `(concatWith [Z] (MAP (GENLIST (K O)) (un_nlist (proj 0 x))))` >>
  fs[INITIAL_TAPE_TM_def]  >>
  fs[pr_INITIAL_TM_NUM_def,pr_INITIAL_TAPE_TM_NUM_def,tape_encode_corr,
     concatWith_Z_corr]
  >- (`∃l. proj 0 x = nlist_of l` by metis_tac[nlist_of_SURJ] >>fs[]>>
      `(l = []) ∨ (l = [0])` by rfs[concatWith_Z_empty] >>
      fs[encode_tl_concat_def,encode_concat_def,ENCODE_def,DIV2_def,
         ncons_def]  >>EVAL_TAC) >>
  simp[ENCODE_def] >>
  `ENCODE t = encode_tl_concat (proj 0 x)`
    by metis_tac[ENCODE_TL_concatWith,listOfN_nlist, nlist_listOfN] >>
  simp[ENCODE_TL_concatWith] >>
  `NUM_CELL h =
   NUM_CELL
     (HD (concatWith [Z] (MAP (GENLIST (K O)) (un_nlist (proj 0 x)))))`
    by simp[] >>
  simp[odd_encode_hd_concat] >>
  `nB (proj 0 (un_nlist (proj 0 x)) ≠ 0) = nB (nhd (proj 0 x) ≠ 0)`
    suffices_by simp[]  >> rw[] >>
  Cases_on `x` >> simp[] >>
  `∃l.  h' =  nlist_of l` by metis_tac[nlist_of_SURJ] >> rw[]>>
  Cases_on `l` >> simp[]
QED

Theorem RUN_NUM_p:
  RUN_NUM p = Pr INITIAL_TM_NUM (Cn (pr1 (tmstepf p)) [proj 1])
Proof
  simp[FUN_EQ_THM,RUN_NUM_def]
QED

Theorem primrec_RUN_NUM:
  primrec (RUN_NUM p) 2
Proof
  fs[RUN_NUM_p] >> irule alt_Pr_rule >> rpt conj_tac
  >- fs[primrec_INITIAL_TM_NUM] >>
  irule primrec_cn >> rpt conj_tac >- fs[primrec_rules] >> fs[primrec_tmstepf]
QED

Theorem Pr_thm_one:
  (Pr b r (1::t) = r (0::Pr b r (0::t)::t))
Proof
rw[Pr_thm] >> `Pr b r (1::t) = Pr b r ((SUC 0)::t)` by metis_tac[ONE] >> rw[]
QED

Theorem zero_less_nB[simp]:
  (0 < nB A) <=> A
Proof
Cases_on `A` >> fs[]
QED

val recfn_rulesl = CONJUNCTS recfn_rules
Theorem recfnCn = List.nth(recfn_rulesl, 3)
Theorem recfnPr = List.nth(recfn_rulesl, 4)

(* Probably need to include a 'tape reset' type function, ie tm_return_num *)
Definition recfn_tm_def:
  recfn_tm p = recCn (SOME o (RUN_NUM p)) [
                        minimise (SOME o (Cn (pr1 nfst) [RUN_NUM p]  )  ) ;
                        SOME o proj 0]
End

Theorem recfn_tm_recfn:
  recfn (recfn_tm p) 1
Proof
  rw[recfn_tm_def] >> fs[primrec_RUN_NUM,primrec_recfn] >> irule recfnCn >>
  rw[recfn_rules]
  >- (irule recfnMin >> fs[] >> irule primrec_recfn >>
      rpt (irule primrec_cn >>
           rw[primrec_rules,primrec_pr_eq,primrec_RUN_NUM,primrec_pr_add]))
  >- (fs[primrec_RUN_NUM,primrec_recfn])
QED

Theorem UPDATE_TAPE_HALTED[simp]:
  (HALTED tm) ==> (UPDATE_TAPE tm = tm)
Proof
rw[] >> fs[UPDATE_TAPE_def,HALTED_def] >> simp[TM_component_equality]
QED

Theorem run_num_halted:
  ∀n. HALTED (RUN n (INITIAL_TM p args)) ∧ n<=m ==>
       (RUN_NUM p [m; nlist_of args] = RUN_NUM p [SUC m; nlist_of args])
Proof
  rpt strip_tac >> `∃k. m=n+k` by metis_tac[LESS_EQ_EXISTS] >>
  rw[RUN_NUM_corr,FUNPOW_SUC] >> qmatch_abbrev_tac `⟦tm⟧ = ⟦UPDATE_TAPE tm⟧` >>
  `HALTED tm` suffices_by simp[] >>
  qunabbrev_tac `tm` >> fs[] >> Induct_on `k` >>
  simp[] >> rw[] >> simp[FUNPOW_SUC,ADD_CLAUSES]
QED

Theorem main_eq_thm:
  ∀p. ∃f. recfn f 1 ∧
           ∀args.
             OPTION_MAP FULL_ENCODE_TM (tm_fn p args) = f [nlist_of args]
Proof
  strip_tac >> qexists_tac`recfn_tm p` >> conj_tac
  >- fs[recfn_tm_recfn] >>
  strip_tac >> fs[tm_fn_def,recfn_tm_def] >>
  Cases_on `(OLEAST n. HALTED (RUN n (INITIAL_TM p args)))` >>
  fs[optionTheory.OPTION_MAP_DEF] >> rw[RUN_NUM_corr] >> fs[recCn_def]
  >- (fs[] >>fs[minimise_def] >> rpt strip_tac >> rfs[RUN_NUM_corr] >>
      first_x_assum (qspec_then `n` mp_tac) >> simp[HALTED_def] >>
      fs[])
  >- (fs[OLEAST_EQ_SOME,minimise_def] >> rw[]
      >- (rename[`RUN n (INITIAL_TM p args)`] >> qexists_tac `n` >>
          fs[HALTED_def,RUN_NUM_corr] >> metis_tac[])
      >- (fs[RUN_NUM_corr] >> qmatch_abbrev_tac `⟦RUN i tm⟧ = ⟦RUN j tm⟧`>>
          `i=j` suffices_by simp[] >> qunabbrev_tac `i` >> SELECT_ELIM_TAC >>
          rw[]
          >- (fs[HALTED_def] >> metis_tac[])
          >- (fs[HALTED_def] >>
              qmatch_abbrev_tac `a=b` >>`¬(a<b)∧¬(b<a)` suffices_by simp[] >>
              rpt strip_tac >> metis_tac[NOT_ZERO_LT_ZERO]))
      >- (fs[RUN_NUM_corr] >> first_x_assum (qspec_then `x` mp_tac)>>
          rpt strip_tac >> fs[HALTED_def] >>
          `∃i. i < x ∧ ((RUN i (INITIAL_TM p args)).state = 0)` by fs[] >>
          metis_tac[]))
QED

(* as final step, should show that we can extract number under head *)

val _ = export_theory();
