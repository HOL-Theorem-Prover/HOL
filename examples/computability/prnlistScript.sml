open HolKernel Parse bossLib boolLib

open primrecfnsTheory numpairTheory arithmeticTheory

fun Store_thm (trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val _ = new_theory "prnlist" (* "primitive recursive number lists" *)

val primrec_ncons = Store_thm(
  "primrec_ncons",
  ``primrec (pr2 ncons) 2``,
  MATCH_MP_TAC primrec_pr2 THEN
  Q.EXISTS_TAC `Cn succ [Cn (pr2 npair) [proj 0; proj 1]]` THEN
  SRW_TAC [][primrec_rules, ncons_def, ADD1]);

(* nhd *)
val nhd_def = Define`nhd nl = nfst (nl - 1)`

val nhd_thm = Store_thm(
  "nhd_thm",
  ``nhd (ncons h t) = h``,
  SRW_TAC [][ncons_def, nhd_def]);

val primrec_nhd = Store_thm(
  "primrec_nhd",
  ``primrec (pr1 nhd) 1``,
  MATCH_MP_TAC primrec_pr1 THEN
  Q.EXISTS_TAC `Cn (pr1 nfst) [Cn (pr2 $-) [proj 0; K 1]]` THEN
  SRW_TAC [][primrec_rules, nhd_def]);

(* ntl *)
val ntl_def = Define`ntl nlist = nsnd (nlist - 1)`

val ntl_thm = Store_thm(
  "ntl_thm",
  ``ntl (ncons h t) = t``,
  SRW_TAC [][ncons_def, ntl_def]);

val primrec_ntl = Store_thm(
  "primrec_ntl",
  ``primrec (pr1 ntl) 1``,
  MATCH_MP_TAC primrec_pr1 THEN
  Q.EXISTS_TAC `Cn (pr1 nsnd) [Cn (pr2 $-) [proj 0; K 1]]` THEN
  SRW_TAC [][primrec_rules, ntl_def]);

(* ndrop *)
val ndrop_def = Define`
  (ndrop 0 nlist = nlist) ∧
  (ndrop (SUC n) nlist = ntl (ndrop n nlist))
`;

val primrec_ndrop = Store_thm(
  "primrec_ndrop",
  ``primrec (pr2 ndrop) 2``,
  MATCH_MP_TAC primrec_pr2 THEN
  Q.EXISTS_TAC `Pr (proj 0) (Cn (pr1 ntl) [proj 1])` THEN
  SRW_TAC [][primrec_rules] THEN
  Induct_on `m` THEN SRW_TAC [][ndrop_def]);

val ndrop_FUNPOW_ntl = store_thm(
  "ndrop_FUNPOW_ntl",
  ``∀n ms. ndrop n ms = FUNPOW ntl n ms``,
  Induct THEN SRW_TAC [][ndrop_def, FUNPOW_SUC]);

(* nel *)
val nel_def = Define`nel n nlist = nhd (ndrop n nlist)`

val nel_thm = Store_thm(
  "nel_thm",
  ``(nel 0 (ncons h t) = h) ∧
    (nel (SUC n) (ncons h t) = nel n t)``,
  SRW_TAC [][nel_def, ndrop_def] THEN
  SRW_TAC [][ndrop_FUNPOW_ntl] THEN
  SRW_TAC [][GSYM FUNPOW_SUC] THEN
  SRW_TAC [][FUNPOW])

val primrec_nel = Store_thm(
  "primrec_nel",
  ``primrec (pr2 nel) 2``,
  MATCH_MP_TAC primrec_pr2 THEN
  Q.EXISTS_TAC `Cn (pr1 nhd) [pr2 ndrop]` THEN
  SRW_TAC [][primrec_rules, nel_def]);

(* nappend *)
val napp_def = Define`
  napp l1 l2 = nlistrec l2 (λn t r. ncons n r) l1
`;

val napp_thm = Store_thm(
  "napp_thm",
  ``(napp 0 nlist = nlist) ∧
    (napp (ncons h t) nlist = ncons h (napp t nlist))``,
  SRW_TAC [][napp_def]);
val primrec_cn = List.nth(CONJUNCTS primrec_rules, 3)


(* representing this primitive recursively is trickier *)
(* val primrec_napp = Store_thm(
  "primrec_napp",
  ``primrec (pr2 napp) 2``,
  MATCH_MP_TAC primrec_pr2 THEN
  Q.EXISTS_TAC `
    Pr (Cn (pr2 ncons) [proj 0; zerof])
       (* n, r, 2nd arg *)
       (let sucn = Cn succ [proj 0] in
        let tl = Cn (pr1 ntl) [sucn] in
        let hd = Cn (pr1 nhd) [sucn] in
        let pos = Cn (pr2 $-) [sucn; tl] in
        let rres = Cn (pr2 nel) [pos; proj 1] in
        let res = Cn (pr2 ncons) [hd; rres]
        in
          Cn (pr2 ncons) [res; proj 1])
  ` THEN
  CONJ_TAC THENL [
    SRW_TAC [][] THEN MATCH_MP_TAC alt_Pr_rule THEN
    SRW_TAC [][primrec_rules] THEN1
      (MATCH_MP_TAC primrec_cn THEN SRW_TAC [][]
    MATCH_MP_TAC primrec_cn THEN SRW_TAC [][primrec_rules] THEN
    Q.UNABBREV_TAC `res` THEN
    MATCH_MP_TAC primrec_cn THEN
    `primrec sucn 3`
      by SRW_TAC [][primrec_rules, Abbr`sucn`] THEN
    SRW_TAC [][primrec_rules] THEN1
      SRW_TAC [][primrec_rules, Abbr`hd`] THEN
    Q.UNABBREV_TAC `rres` THEN MATCH_MP_TAC primrec_cn THEN
    SRW_TAC [][primrec_rules] THEN
    `primrec tl 3` by SRW_TAC [][primrec_rules, Abbr`tl`] THEN
    SRW_TAC [][primrec_rules, Abbr`pos`],

    HO_MATCH_MP_TAC nlist_ind THEN SRW_TAC [][LET_THM] THEN1
      SRW_TAC [][ncons_def]


*)
val _ = export_theory ()
