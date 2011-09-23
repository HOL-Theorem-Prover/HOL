open HolKernel boolLib bossLib Parse finite_mapTheory relationTheory termTheory substTheory alistTheory arithmeticTheory pred_setTheory rich_listTheory listTheory ramanaLib

val _ = new_theory "walk"
val _ = metisTools.limit :=  { time = NONE, infs = SOME 1 }

fun vwalk_wfs_hyp th =
let val th =
  Q.INST [`R` |-> `vR s`] th
in
  foldl (fn (h,th) => PROVE_HYP h th) th
    (map
      (UNDISCH o (fn t => prove (``wfs s ==> ^t``, SRW_TAC [] [wfs_def,vR_def])))
      (hyp th))
end

val vwalk_def = save_thm("vwalk_def",vwalk_wfs_hyp
(TotalDefn.xDefineSchema "pre_vwalk"
 `vwalk v =
    case FLOOKUP s v of
         SOME (Var u) => vwalk u
       | SOME t => t
       | NONE => Var v`) |> DISCH_ALL)
val vwalk_ind = save_thm("vwalk_ind",vwalk_wfs_hyp (theorem "pre_vwalk_ind"))

val _ = store_term_thm("vwalk_def_print",
TermWithCase`
  wfs s ⇒
  (vwalk s v =
   case FLOOKUP s v of
         SOME (Var u) => vwalk s u
       | SOME t => t
       | NONE => Var v)`)

val NOT_FDOM_vwalk = Q.store_thm(
  "NOT_FDOM_vwalk",
  `wfs s /\ v NOTIN FDOM s ==> (vwalk s v = Var v)`,
  SRW_TAC [] [Once vwalk_def, FLOOKUP_DEF]);

val vwalk_to_var = Q.store_thm(
  "vwalk_to_var",
  `wfs s ==> !v u. (vwalk s v = Var u) ==> u NOTIN FDOM s`,
  DISCH_TAC THEN HO_MATCH_MP_TAC vwalk_ind THEN
  SRW_TAC [][] THEN
  Cases_on `FLOOKUP s v` THEN1
    (REPEAT (POP_ASSUM MP_TAC) THEN
     REPEAT (SRW_TAC [][Once vwalk_def, FLOOKUP_DEF])) THEN
  `?w.x = Var w`
     by (Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [Once (UNDISCH vwalk_def)]) THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `w` MP_TAC) THEN SRW_TAC [][] THEN
  `vwalk s w = Var u` by (REPEAT (POP_ASSUM MP_TAC) THEN
                          SRW_TAC [] [Once vwalk_def] THEN
                          FULL_SIMP_TAC (srw_ss()) []) THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `u` MP_TAC) THEN SRW_TAC [][]);

val walk_def = Define`
  walk s t = case t of Var v => vwalk s v | t => t`;

val walk_thm = RWstore_thm(
"walk_thm",
`(walk s (Var v) = vwalk s v) /\
 (walk s (Pair t1 t2) = (Pair t1 t2)) /\
 (walk s (Const c) = (Const c))`,
SRW_TAC [][walk_def]);

val walk_FEMPTY = RWstore_thm(
"walk_FEMPTY",
`(walk FEMPTY t = t) /\
 (vwalk FEMPTY v = Var v)`,
Cases_on `t` THEN NTAC 2 (SRW_TAC [][Once(DISCH_ALL vwalk_def)]));

val walk_var_vwalk = Q.store_thm(
"walk_var_vwalk",
`wfs s ==> (walk s t = Var v)
  ==> ?u.(t = Var u) /\ (vwalk s u = Var v)`,
SRW_TAC [][walk_def] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []);

val walk_to_var = Q.store_thm(
"walk_to_var",
`wfs s /\ (walk s t = Var v) ==>
   v NOTIN FDOM s /\ ?u.(t = Var u)`,
Cases_on `t` THEN SRW_TAC [][] THEN
METIS_TAC [vwalk_to_var]);

val vwalk_vR = Q.store_thm(
"vwalk_vR",
`wfs s ==> !v u. u IN vars (vwalk s v) /\ vwalk s v <> Var v ==>
           (vR s)^+ u v`,
DISCH_TAC THEN HO_MATCH_MP_TAC vwalk_ind THEN SRW_TAC [][] THEN
`(FLOOKUP s v = NONE) \/ ?t. FLOOKUP s v = SOME t`
   by (Cases_on `FLOOKUP s v` THEN SRW_TAC [][]) THEN1
(`vwalk s v = Var v` by (ONCE_REWRITE_TAC [UNDISCH vwalk_def] THEN
 SRW_TAC [][])) THEN
Cases_on `t` THENL [
  `vwalk s v = vwalk s n` by (SRW_TAC [][Once vwalk_def]) THEN
  `vR s n v` by SRW_TAC [][vR_def] THEN
  Cases_on `vwalk s n = Var n` THENL [
    `u = n` by FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][TC_SUBSET],
    `(vR s)^+ u n` by METIS_TAC [] THEN
    MATCH_MP_TAC
        (GEN_ALL (CONJUNCT2 (SPEC_ALL TC_RULES))) THEN
    METIS_TAC [TC_SUBSET]
  ],
  `vwalk s v = Pair t' t0` by (SRW_TAC [][Once vwalk_def]) THEN
  MATCH_MP_TAC TC_SUBSET THEN
  SRW_TAC [][vR_def] THEN FULL_SIMP_TAC (srw_ss()) [],
  Q.MATCH_ASSUM_RENAME_TAC `FLOOKUP s v = SOME (Const c)` [] THEN
  `vwalk s v = Const c` by (SRW_TAC [] [Once vwalk_def]) THEN
  FULL_SIMP_TAC (srw_ss()) []
]);

val vwalk_IN_FRANGE = Q.store_thm(
"vwalk_IN_FRANGE",
`wfs s ∧ v ∈ FDOM s ⇒ vwalk s v ∈ FRANGE s`,
SIMP_TAC (srw_ss()) [GSYM AND_IMP_INTRO] THEN
STRIP_TAC THEN Q.ID_SPEC_TAC `v` THEN
HO_MATCH_MP_TAC vwalk_ind THEN SRW_TAC [][] THEN
SRW_TAC [][Once vwalk_def] THEN
FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF] THEN
Cases_on `s ' v` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
  Cases_on `n ∈ FDOM s` THEN SRW_TAC [][NOT_FDOM_vwalk],
  ALL_TAC, ALL_TAC ] THEN
SRW_TAC [][FRANGE_DEF] THEN METIS_TAC []);

val walk_IN_FRANGE = Q.store_thm(
"walk_IN_FRANGE",
`wfs s ∧ walk s t ≠ t ⇒ walk s t ∈ FRANGE s`,
Cases_on `t` THEN SRW_TAC [][] THEN
`n ∈ FDOM s` by METIS_TAC [NOT_FDOM_vwalk] THEN
SRW_TAC [][vwalk_IN_FRANGE]);

val vwalk_SUBMAP = Q.store_thm(
"vwalk_SUBMAP",
`wfs sx ==> !v s.s SUBMAP sx ==>
   (case vwalk s v of Var u => (vwalk sx v = vwalk sx u)
                    | t => (vwalk sx v = t))`,
STRIP_TAC THEN HO_MATCH_MP_TAC (Q.INST[`s`|->`sx`]vwalk_ind) THEN
SRW_TAC [][] THEN
`wfs s` by METIS_TAC [wfs_SUBMAP] THEN
POP_ASSUM MP_TAC THEN
SIMP_TAC (srw_ss())[Once vwalk_def] THEN
Cases_on `FLOOKUP s v` THEN SRW_TAC [][] THEN
Cases_on `x` THEN SRW_TAC [][] THENL [
  `FLOOKUP sx v = SOME (Var n)`
     by METIS_TAC [FLOOKUP_SUBMAP] THEN
  `vwalk sx v = vwalk sx n`
     by SRW_TAC [][Once (DISCH_ALL vwalk_def), SimpLHS] THEN
  METIS_TAC [],
  `FLOOKUP sx v = SOME (Pair t t0)` by METIS_TAC [FLOOKUP_SUBMAP] THEN
  SRW_TAC [][Once (DISCH_ALL vwalk_def)],
  Q.MATCH_ASSUM_RENAME_TAC `FLOOKUP s v = SOME (Const c)` [] THEN
  `FLOOKUP sx v = SOME (Const c)` by METIS_TAC [FLOOKUP_SUBMAP] THEN
  SRW_TAC [][Once (DISCH_ALL vwalk_def)]
]);

(* vwalk with concrete alists *)

val _ = overload_on("vwalk_al", ``λal. vwalk (alist_to_fmap al)``);
val _ = overload_on("vwalk_al", ``vwalk_al``);

val vwalk_al_thm = Q.store_thm(
"vwalk_al_thm",
`wfs (alist_to_fmap al) ==>
  (vwalk_al al v =
   case ALOOKUP al v of
     NONE => Var v |
     SOME (Var u) => vwalk_al al u |
     SOME t => t)`,
METIS_TAC [fmap_to_alist_to_fmap,vwalk_def,ALOOKUP_EQ_FLOOKUP]);

val vwalk_al_eq_vwalk = Q.store_thm(
"vwalk_al_eq_vwalk",
`vwalk s = vwalk_al (fmap_to_alist s)`,
METIS_TAC [fmap_to_alist_to_fmap]);

(* vwalk with rhs check *)

val vwalk_rhs_q = `
  (vwalk_rhs s [] v = Var v) ∧
  (vwalk_rhs s ((x,Var u)::t) v =
   if u = v then Var v
   else if x = v then vwalk_rhs s s u
   else vwalk_rhs s t v) ∧
  (vwalk_rhs s ((x,y)::t) v =
   if x = v then y
   else vwalk_rhs s t v)`;

val ELENGTH_def = Define`
  (ELENGTH (v, []) = 0) ∧
  (ELENGTH (v, (h::t)) = if SND h = Var v then 0 else 1 + ELENGTH (v, t))`;
val _ = export_rewrites ["ELENGTH_def"];

val vwalk_rhsR_q = `
  inv_image
     (measure (λb. if b then 0 else 1) LEX
      measure ELENGTH LEX measure LENGTH)
     (λ(s0,s1,v). ((∃pr. (s0 = pr ++ s1) ∧
                       ∀e. MEM e pr ⇒ FST e ≠ v ∧ SND e ≠ Var v),
                  (v, s0), s1))`;

val vwalk_rhs_def = tDefine "vwalk_rhs" vwalk_rhs_q
(WF_REL_TAC vwalk_rhsR_q THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Induct_on `pr` THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC []);

val _ = store_term_thm("vwalk_rhsR", Term vwalk_rhsR_q);
val _ = store_term_thm("vwalk_rhs_defn_print", Term vwalk_rhs_q);

val vwalk_rhs_ind = theorem "vwalk_rhs_ind";

open lcsymtacs

val example1 = Q.prove(
`(y ≠ x) ⇒ (vwalk_al [(y,Var x);(x,Const c)] x = Const c)`,
strip_tac >>
Q.MATCH_ABBREV_TAC `vwalk_al s x = Const c` >>
`wfs (alist_to_fmap s)` by (
  srw_tac [][wfs_no_cycles] >>
  SPOSE_NOT_THEN STRIP_ASSUME_TAC >>
  imp_res_tac TC_CASES1 >>
  full_simp_tac (srw_ss()) [vR_def] >>
  full_simp_tac std_ss [GSYM (CONJUNCT1 ALOOKUP_EQ_FLOOKUP)] >>
  full_simp_tac (srw_ss()) [Abbr`s`] >- (
    Cases_on `y = v` >> full_simp_tac (srw_ss()) [] >>
    Cases_on `x = v` >> full_simp_tac (srw_ss()) [] ) >>
  Cases_on `y = y'` >> full_simp_tac (srw_ss()) [] >> srw_tac [][] >- (
    POP_ASSUM (K ALL_TAC) >>
    imp_res_tac TC_CASES2 >>
    full_simp_tac (srw_ss()) [vR_def] >>
    fsrw_tac [][FLOOKUP_UPDATE] >> pop_assum mp_tac >> srw_tac [][] ) >>
  Cases_on `x = y'` >> full_simp_tac (srw_ss()) [] ) >>
srw_tac [][Once vwalk_al_thm] >>
srw_tac [][Abbr`s`])

val example2 = Q.prove(
`(y ≠ x) ⇒ (vwalk_rhs [(y,Var x);(x,Const c)] [(y,Var x);(x,Const c)] x = Var x)`,
srw_tac [][Once vwalk_rhs_def])

val vwalk_rhs_ALOOKUP_NONE = Q.store_thm(
"vwalk_rhs_ALOOKUP_NONE",
`∀a0 al v. (ALOOKUP al v = NONE) ⇒ (vwalk_rhs a0 al v = Var v)`,
ho_match_mp_tac vwalk_rhs_ind >> srw_tac [][vwalk_rhs_def])

(*
val vwalk_rhs_ALOOKUP_SOME_nonvar = Q.store_thm(
"vwalk_rhs_ALOOKUP_SOME_nonvar",
`∀al a0 v t. (ALOOKUP al v = SOME t) ∧ (∀u. t ≠ Var u) ⇒ (vwalk_rhs a0 al v = t)`,
Induct >> srw_tac [][] >>
Cases_on `h` >> Cases_on `r` >> srw_tac [][vwalk_rhs_def]
ho_match_mp_tac vwalk_rhs_ind >>
srw_tac [][] >>
srw_tac [][vwalk_rhs_def] >>
Cases_on `t` >> srw_tac [][]
FALSE

val submaps_def = RWDefine`
  (submaps [] = T) ∧
  (submaps ((x,Var v)::t) = v ∉ set (MAP FST t) ∧ submaps t) ∧
  (submaps (h::t) = submaps t)`; THIS IS PROBABLY WRONG

val submaps_thm = Q.store_thm(
"submaps_thm",
`submaps al ⇔ ∀l1 l2. (al = l1 ++ l2) ⇒ (alist_to_fmap l2) SUBMAP (alist_to_fmap al)`,
Induct_on `al` >> srw_tac [][] >>
Cases_on `h` >> Cases_on `r` >> srw_tac [][] >- (
  srw_tac [][EQ_IMP_THM] >- (
    Cases_on `l1` >> full_simp_tac (srw_ss()) [] >>
    srw_tac [][] >>
    POP_ASSUM (Q.SPECL_THEN [`t`,`l2`] mp_tac) >>
    srw_tac [][] >>
    match_mp_tac SUBMAP_TRANS >>
    qexists_tac `alist_to_fmap (t ++ l2)` >> srw_tac [][] >>
    Q.MATCH_ABBREV_TAC `f SUBMAP g` >>
    qsuff_tac `!k v. (FLOOKUP f k = SOME v) ⇒ (FLOOKUP g k = SOME v)` >- (
      srw_tac [][FLOOKUP_DEF,SUBMAP_DEF] ) >>
    srw_tac [][Abbr`g`,Abbr`f`,GSYM (CONJUNCT1 ALOOKUP_EQ_FLOOKUP)]

val vwalk_rhs_eq_vwalk_al = Q.store_thm(
"vwalk_rhs_eq_vwalk"
`wfs (alist_to_fmap al) ∧ submaps al ⇒ (vwalk_rhs al al v = vwalk_al al v)`
*)

val _ = export_theory ();
