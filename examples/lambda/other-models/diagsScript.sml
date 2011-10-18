open HolKernel Parse boolLib

open relationTheory bossLib boolSimps

open pred_setTheory

val _ = new_theory "diags"

(* Diagram evaluation *)
val _ = Hol_datatype `reltype = Atomic | TC`

val liftrel_def = Define`
  liftrel b ty R x y = (if b then I else (~))
                         ((case ty of Atomic => I | TC => TC)
                          R x y)
`;


val eval_def = Define`
  eval (Fa : ('n # 'a # 'a # bool # reltype) -> bool)
       (G : ('n # ('a + 'b) # ('a + 'b) # bool # reltype) -> bool)
       (R : 'n -> 'c -> 'c -> bool) =
    ! (f : 'a -> 'c).
         (!a1 a2 n b ty. (n, a1, a2, b, ty) IN Fa ==>
                         liftrel b ty (R n) (f a1) (f a2)) ==>
         ? (g : 'b -> 'c).
             (!a1 a2 n b ty. (n, INL a1, INL a2, b, ty) IN G ==>
                             liftrel b ty (R n) (f a1) (f a2)) /\
             (!a b n p ty. (n, INL a, INR b, p, ty) IN G ==>
                           liftrel p ty (R n) (f a) (g b)) /\
             (!a b n p ty. (n, INR b, INL a, p, ty) IN G ==>
                           liftrel p ty (R n) (g b) (f a)) /\
             (!b1 b2 n b ty. (n, INR b1, INR b2, b, ty) IN G ==>
                             liftrel b ty (R n) (g b1) (g b2))
`;

(* Some example diagrams *)

val diamond_eval = store_thm(
  "diamond_eval",
  ``eval {(0,0,1,T,Atomic); (0,0,2,T,Atomic)}
         {(0,INL 1,INR 0,T,Atomic); (0,INL 2,INR 0,T,Atomic)}
         R
     = diamond (R 0)``,
  SRW_TAC [DNF_ss] [diamond_def, eval_def, EQ_IMP_THM, liftrel_def] THENL [
    FIRST_X_ASSUM (Q.SPEC_THEN `\n. if n = 0 then x
                                    else if n = 1 then y
                                    else z`
                   MP_TAC) THEN
    SRW_TAC [DNF_ss][] THEN METIS_TAC [],
    `?u. R 0 (f 1) u /\ R 0 (f 2) u` by METIS_TAC [] THEN
    Q.EXISTS_TAC `K u` THEN SRW_TAC [][]
  ]);

val totality_eval = store_thm(
  "totality_eval",
  ``eval {} {(0, INL 0, INL 1, T, Atomic)} R = !x y. R 0 x y``,
  SRW_TAC [DNF_ss][eval_def, EQ_IMP_THM, liftrel_def] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `\i. if i = 0 then x else y` MP_TAC) THEN
  SRW_TAC [][]);

val lopsided_TC_diamond = store_thm(
  "lopsided_TC_diamond",
  ``eval {(0,0,1,T,Atomic); (0,0,2,T,TC)}
         {(0,INL 1,INR 0,T,TC); (0,INL 2,INR 0,T,TC)} R =
    !x y z. R 0 x y /\ TC (R 0) x z ==>
            ?u. TC (R 0) y u /\ TC (R 0) z u``,
  SRW_TAC [DNF_ss][eval_def, EQ_IMP_THM, liftrel_def] THENL [
    FIRST_X_ASSUM (Q.SPEC_THEN `\n. if n = 0 then x
                                    else if n = 1 then y
                                    else z`
                   MP_TAC) THEN
    SRW_TAC [DNF_ss][] THEN METIS_TAC [],
    `?u. TC (R 0) (f 1) u /\ TC (R 0) (f 2) u` by METIS_TAC [] THEN
    Q.EXISTS_TAC `K u` THEN SRW_TAC [][]
  ]);

val sequentialisation_eval = store_thm(
  "sequentialisation_eval",
  ``eval {(0,0,1,T,Atomic)}
         {(1,INL 0,INR 0,T,Atomic); (2,INR 0,INL 1,T,Atomic)}
         R =
    (!x y. R 0 x y ==> ?z. R 1 x z /\ R 2 z y)``,
  SRW_TAC [DNF_ss][eval_def, EQ_IMP_THM,liftrel_def] THENL [
    FIRST_X_ASSUM (Q.SPEC_THEN `\n. if n = 0 then x else y` MP_TAC) THEN
    SRW_TAC [DNF_ss][] THEN METIS_TAC [],
    `?z. R 1 (f 0) z /\ R 2 z (f 1)` by METIS_TAC [] THEN
    Q.EXISTS_TAC `K z` THEN SRW_TAC [][]
  ]);

val only_black_eq_T = prove(
  ``eval Fa {} R' = T``,
  SRW_TAC [DNF_ss][eval_def]);

val relationally_reflected = store_thm(
  "relationally_reflected",
  ``eval {(0,0,1,T,Atomic)}
         {(1,INR 0,INL 0,T,Atomic); (1,INR 1,INL 1,T,Atomic);
          (2,INR 0,INR 1,T,Atomic)}
         R =
    (!x y. R 0 x y ==> ?u v. R 1 u x /\ R 1 v y /\ R 2 u v)``,
  SRW_TAC [DNF_ss][eval_def, EQ_IMP_THM, liftrel_def] THENL [
    FIRST_X_ASSUM (Q.SPEC_THEN `\n. if n = 0 then x else y` MP_TAC) THEN
    SRW_TAC [DNF_ss][] THEN METIS_TAC [],
    `?u v. R 1 u (f 0) /\ R 1 v (f 1) /\ R 2 u v` by METIS_TAC [] THEN
    Q.EXISTS_TAC `\n. if n = 0 then u else v` THEN
    SRW_TAC [][]
  ]);

val no_1step_join = store_thm(
  "no_1step_join",
  ``eval {(0,0,1,T,Atomic); (0,0,2,T,Atomic)}
         {(0,INL 1,INL 2,F,Atomic)} R =
    (!x y z. R 0 x y /\ R 0 x z ==> ~R 0 y z)``,
  SRW_TAC [DNF_ss][eval_def, EQ_IMP_THM, liftrel_def] THENL [
    FIRST_X_ASSUM (Q.SPEC_THEN `\n. if n = 0 then x
                                    else if n = 1 then y else z` MP_TAC) THEN
    SRW_TAC [DNF_ss][],
    METIS_TAC []
  ]);

val no_terminal_object = store_thm(
  "no_terminal_object",
  ``eval {} {(0,INR 0,INL 0,F,Atomic)} R  = !y. ?x. ~R 0 x y``,
  SRW_TAC [DNF_ss][eval_def, EQ_IMP_THM, liftrel_def] THENL [
    FIRST_X_ASSUM (Q.SPEC_THEN `\n. y` MP_TAC) THEN SRW_TAC [][] THEN
    METIS_TAC [],
    `?u. ~R 0 u (f 0)` by METIS_TAC [] THEN
    Q.EXISTS_TAC `\n. u` THEN SRW_TAC [][]
  ]);


(* ----------------------------------------------------------------------
    Propositional Diagrams
   ---------------------------------------------------------------------- *)

val _ = Hol_datatype`
  diaform = Lf of (('n # 'a # 'a # bool # reltype) -> bool) =>
                  (('n # ('a + 'b) # ('a + 'b) # bool # reltype) -> bool)
          | /\ of diaform => diaform
          | ~ of diaform
`

val evalform_def = Define`
  (evalform (Lf fa ex) R <=> eval fa ex R) /\
  (evalform (f1 /\ f2) R <=> evalform f1 R /\ evalform f2 R) /\
  (evalform (~f) R <=> ~evalform f R)
`;

val R0_refl_def = Define`
  R0_refl = Lf {} {(0,INL 0,INL 0,T,Atomic)}
`

val R0_refl_thm = store_thm(
  "R0_refl_thm",
  ``evalform R0_refl R = !x. R 0 x x``,
  SRW_TAC [][evalform_def, eval_def, R0_refl_def, liftrel_def, EQ_IMP_THM])

val R0_sym_def = Define`
  R0_sym = Lf {(0,0,1,T,Atomic)} {(0,INL 1, INL 0,T,Atomic)}
`;

val R0_sym_thm = store_thm(
  "R0_sym_thm",
  ``evalform R0_sym R = !x y. R 0 x y ==> R 0 y x``,
  SRW_TAC [][evalform_def, eval_def, R0_sym_def, liftrel_def, EQ_IMP_THM] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `\n. if n = 0 then x else y` MP_TAC) THEN
  SRW_TAC [][])

val R0_trans_def = Define`
  R0_trans = Lf {(0,0,1,T,Atomic); (0,1,2,T,Atomic)}
                {(0,INL 0, INL 2,T,Atomic)}
`;
val R0_trans_thm = store_thm(
 "R0_trans_thm",
  ``evalform R0_trans R = !x y z. R 0 x y /\ R 0 y z ==> R 0 x z``,
  SRW_TAC [][evalform_def, eval_def, R0_trans_def, liftrel_def,
             EQ_IMP_THM, DISJ_IMP_THM, FORALL_AND_THM]
  THENL [
    FIRST_X_ASSUM (Q.SPEC_THEN `\n. if n = 0 then x
                                    else if n = 1 then y
                                    else z` MP_TAC) THEN
    SRW_TAC [][],
    METIS_TAC []
  ]);


val R0_cong_def = Define`
  R0_cong n <=> Lf {(0,0,1,T,Atomic); (n,0,2,T,Atomic)}
                   {(n,INL 1,INL 2,T,Atomic)} /\
                Lf {(0,1,2,T,Atomic); (n,0,1,T,Atomic)}
                   {(n,INL 0, INL 2,T,Atomic)}
`
val R0_cong_thm = store_thm(
  "R0_cong_thm",
  ``evalform (R0_cong n) R <=> (!x y z. R 0 x y /\ R n x z ==> R n y z) /\
                               (!x y z. R n x y /\ R 0 y z ==> R n x z)``,
  SRW_TAC [][evalform_def, eval_def, R0_cong_def, liftrel_def,
             EQ_IMP_THM, DISJ_IMP_THM, FORALL_AND_THM]
  THENL [
    FIRST_X_ASSUM (fn th =>
       Q.SPEC_THEN `\n. if n = 0 then x
                        else if n = 1 then y else z` MP_TAC th THEN
       SRW_TAC [][] THEN NO_TAC),
    FIRST_X_ASSUM (fn th =>
       Q.SPEC_THEN `\n. if n = 0 then x
                        else if n = 1 then y else z` MP_TAC th THEN
       SRW_TAC [][] THEN NO_TAC),
    METIS_TAC [],
    METIS_TAC []
  ]);

val imp_def = xDefine "imp" `
  (f1:('a,'b,'c)diaform) ==> f2 <=> ~(f1 /\ ~f2)
`
val imp_thm = store_thm(
  "imp_thm",
  ``evalform (f ==> g) R <=> evalform f R ==> evalform g R``,
  SRW_TAC [][imp_def, evalform_def] THEN METIS_TAC []);


val R0_refl_cong_sym = store_thm(
  "R0_refl_cong_sym",
  ``evalform (R0_cong 0 /\ R0_refl ==> R0_sym) R``,
  SRW_TAC [][imp_thm, R0_cong_thm, evalform_def, R0_refl_thm, R0_sym_thm] THEN
  METIS_TAC [])

val R0_cong_trans = store_thm(
  "R0_cong_trans",
  ``evalform (R0_cong 0 ==> R0_trans) R``,
  METIS_TAC [imp_thm, R0_cong_thm, R0_trans_thm])

(* ----------------------------------------------------------------------
    Theory of diagram equivalence
   ---------------------------------------------------------------------- *)


(* basic concepts *)
val Pres_def = Define`
  Pres f R1 R2 = !x y. R1 x y ==> R2 (f x) (f y)
`;

val onto_def = Define`
  onto f = !x. ?y. f y = x
`;

val sRefl_def = Define`
  sRefl f R1 R2 = !b1 b2. R2 b1 b2 ==>
                         ?a1 a2. R1 a1 a2 /\ (b1 = f a1) /\ (b2 = f a2)
`;

val aRefl_def = Define`
  aRefl f R1 R2 = !x y. R2 (f x) (f y) ==> R1 x y
`;

val kCompl_def = Define`
  kCompl s f = !x y. (f x = f y) ==> EQC s x y
`;

val kSound_def = Define`
  kSound s f = !x y. s x y ==> (f x = f y)
`;

val ofree_def = Define`
  ofree s = !x y. EQC s x y ==> RTC s x y
`;

val presrefl_atomic = store_thm(
  "presrefl_atomic",
  ``Pres f R1 R2 /\ aRefl f R1 R2 ==> !x y. R1 x y = R2 (f x) (f y)``,
  SRW_TAC [][Pres_def, aRefl_def] THEN METIS_TAC []);

val presrefl_TC = store_thm(
  "presrefl_TC",
  ``onto f /\ Pres f R1 R2 /\ aRefl f R1 R2 ==>
    (!x y. TC R1 x y = TC R2 (f x) (f y))``,
  SIMP_TAC (srw_ss()) [onto_def] THEN STRIP_TAC THEN
  `!x y. R1 x y = R2 (f x) (f y)` by METIS_TAC [presrefl_atomic] THEN
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM] THEN CONJ_TAC THENL [
    HO_MATCH_MP_TAC TC_INDUCT THEN METIS_TAC [TC_RULES],
    Q_TAC SUFF_TAC `!a b. TC R2 a b ==> !x y. (a = f x) /\ (b = f y) ==>
                                              TC R1 x y`
          THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC TC_INDUCT THEN
    SRW_TAC [][] THENL [
      METIS_TAC [TC_RULES],
      `?a0. f a0 = a'` by METIS_TAC [] THEN
      METIS_TAC [TC_RULES]
    ]
  ]);

val presrefl_liftrel = store_thm(
  "presrefl_liftrel",
  ``onto f /\ Pres f R1 R2 /\ aRefl f R1 R2 ==>
    !x y b ty. liftrel b ty R1 x y = liftrel b ty R2 (f x) (f y)``,
  SRW_TAC [][liftrel_def] THEN
  Cases_on `ty` THEN SRW_TAC [][presrefl_TC, presrefl_atomic]);

val aRefl_TC = store_thm(
  "aRefl_TC",
  ``aRefl f R1 R2 /\ onto f ==> aRefl f (TC R1) (TC R2)``,
  SIMP_TAC (srw_ss()) [aRefl_def, onto_def] THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!a b. TC R2 a b ==> !x y. (a = f x) /\ (b = f y) ==>
                                            TC R1 x y`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC TC_INDUCT THEN SRW_TAC [][] THEN
  METIS_TAC [TC_RULES]);


(* important theorem *)
val diagram_preservation = store_thm(
  "diagram_preservation",
  ``!R1 R2 h.
       onto h /\ (!n. Pres h (R1 n) (R2 n) /\ aRefl h (R1 n) (R2 n)) ==>
       !Fa G. eval Fa G R1 = eval Fa G R2``,
  REPEAT STRIP_TAC THEN
  `!n a1 a2 b ty. liftrel b ty (R1 n) a1 a2 =
                  liftrel b ty (R2 n) (h a1) (h a2)`
     by METIS_TAC [presrefl_liftrel] THEN
  `?invh. !b. h (invh b) = b` by METIS_TAC [SKOLEM_THM, onto_def] THEN
  ASM_SIMP_TAC (srw_ss()) [eval_def] THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
    FIRST_X_ASSUM (MP_TAC o SPEC ``(invh : 'c -> 'b) o (f : 'd -> 'c)``) THEN
    SRW_TAC [][] THEN
    Q.EXISTS_TAC `h o g` THEN SRW_TAC [][],

    FIRST_X_ASSUM (MP_TAC o SPEC ``(h : 'b -> 'c) o (f : 'd -> 'b)``) THEN
    SRW_TAC [][] THEN
    Q.EXISTS_TAC `invh o g` THEN SRW_TAC [][]
  ]);

(* can prove that diagram formulas are also preserved *)
val diaform_preservation = store_thm(
  "diaform_preservation",
  ``!R1 R2 h.
       onto h /\ (!n. Pres h (R1 n) (R2 n) /\ aRefl h (R1 n) (R2 n)) ==>
       !f. evalform f R1 = evalform f R2``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Induct THEN SRW_TAC [][evalform_def] THEN
  METIS_TAC [diagram_preservation])

(* but aRefl is a strong requirement to make of a homomorphism...
     (some might argue that onto is as well)
   so let's try to weaken aRefl to sRefl.  We can do so by adding
   structure *)

val Refl_is_someany_with_structure = store_thm(
  "Refl_is_someany_with_structure",
  ``kSound s f /\ kCompl s f /\ onto f ==>
    (sRefl f R1 R2 = aRefl f (EQC s O R1 O EQC s) R2)``,
  SRW_TAC [][EQ_IMP_THM, kSound_def, kCompl_def, onto_def, sRefl_def,
             aRefl_def]
  THENL [
    RES_TAC THEN SRW_TAC [][O_DEF] THEN METIS_TAC [],
    `?a1 a2. (b1 = f a1) /\ (b2 = f a2)` by METIS_TAC [] THEN
    SRW_TAC [][] THEN RES_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [O_DEF] THEN
    Q_TAC SUFF_TAC `!x y. EQC s x y ==> (f x = f y)`
          THEN1 METIS_TAC [] THEN
    HO_MATCH_MP_TAC EQC_INDUCTION THEN METIS_TAC []
  ]);

val Pres_ok_with_structure = store_thm(
  "Pres_ok_with_structure",
  ``kSound s f /\ Pres f R1 R2 ==> Pres f (EQC s O R1 O EQC s) R2``,
  SRW_TAC [][Pres_def, kSound_def, O_DEF] THEN
  Q_TAC SUFF_TAC `!x y. EQC s x y ==> (f x = f y)` THEN1
        METIS_TAC [] THEN
  HO_MATCH_MP_TAC EQC_INDUCTION THEN METIS_TAC []);


(* pre-order reduction *)

(* paper's name for this theorem is
     "Pre-ordered structural reflection is some/any"
*)
val note_lemma9 = store_thm(
  "note_lemma9",
  ``onto f  /\ kCompl s f /\ ofree s ==>
    (sRefl f (RTC (x RUNION s)) (RTC y) =
     aRefl f (RTC (x RUNION s)) (RTC y))``,
  SIMP_TAC (srw_ss()) [onto_def, kCompl_def, ofree_def, sRefl_def,
                       aRefl_def] THEN STRIP_TAC THEN EQ_TAC
  THENL [
    STRIP_TAC THEN MAP_EVERY Q.X_GEN_TAC [`a1`, `a2`] THEN STRIP_TAC THEN
    `?a1' a2'. RTC (x RUNION s) a1' a2' /\ (f a1' = f a1) /\ (f a2' = f a2)`
       by METIS_TAC [] THEN
    `RTC s a1 a1' /\ RTC s a2' a2` by METIS_TAC [] THEN
    `RTC (x RUNION s) a1 a1' /\ RTC (x RUNION s) a2' a2`
       by METIS_TAC [chap3Theory.RUNION_RTC_MONOTONE, RUNION_COMM] THEN
    METIS_TAC [RTC_RTC],
    METIS_TAC []
  ]);

(* paper's name for this theorem is
     "Some-Reflection is Structurally Pre-ordered"
*)
val note_prop10_1 = store_thm(
  "note_prop10_1",
  ``onto f /\ kCompl s f /\ ofree s /\ sRefl f x y ==>
    sRefl f (RTC (x RUNION s)) (RTC y)``,
  SIMP_TAC (srw_ss()) [sRefl_def, onto_def, ofree_def, kCompl_def] THEN
  STRIP_TAC THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN CONJ_TAC THENL [
    METIS_TAC [chap3Theory.RUNION_RTC_MONOTONE, RUNION_COMM],
    REPEAT STRIP_TAC THEN
    `?a0 a1'. x a0 a1' /\ (b1 = f a0) /\ (b1' = f a1')` by METIS_TAC [] THEN
    `RTC s a1' a1` by METIS_TAC [] THEN
    `RTC (x RUNION s) a1' a1`
      by METIS_TAC [chap3Theory.RUNION_RTC_MONOTONE, RUNION_COMM] THEN
    `RTC (x RUNION s) a0 a1'` by METIS_TAC [chap3Theory.RUNION_RTC_MONOTONE,
                                            RTC_RULES] THEN
    METIS_TAC [RTC_RTC]
  ]);

(* "structural pre-ordered preservation" *)
val Pres_structure_RTC = store_thm(
  "Pres_structure_RTC",
  ``Pres f R1 R2 /\ kSound s f ==>
    Pres f (RTC (R1 RUNION s)) (RTC R2)``,
  SIMP_TAC (srw_ss()) [Pres_def, kSound_def] THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][RTC_RULES, RUNION] THEN
  METIS_TAC [RTC_RULES]);

val _ = export_theory()
