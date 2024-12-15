open HolKernel boolLib bossLib Parse stringTheory nomsetTheory listTheory ramanaLib relationTheory quotientLib pairTheory bagTheory commonUnifTheory;

val _ = new_theory "nterm";
val _ = metisTools.limit :=  { time = NONE, infs = SOME 5000 };

val permeq_exists = RWstore_thm(
"permeq_exists",
`(∃x. p == x) ∧ (∃x. x == p)`,
METIS_TAC [permeq_refl]);

val _ = Hol_datatype`
  Cterm = CNom of string
        | CSus of (string # string) list => num
        | CTie of string => Cterm
        | CnPair of Cterm => Cterm
        | CnConst of 'a`;

Definition Ctermeq_def[simp]:
  (Ctermeq (CNom a1) (CNom a2) = (a1 = a2)) ∧
  (Ctermeq (CSus p1 v1) (CSus p2 v2) <=> (p1 == p2) ∧ (v1 = v2)) ∧
  (Ctermeq (CTie a1 t1) (CTie a2 t2) <=> (a1 = a2) ∧ Ctermeq t1 t2) ∧
  (Ctermeq (CnPair t1a t1d) (CnPair t2a t2d) <=>
     Ctermeq t1a t2a ∧ Ctermeq t1d t2d) ∧
  (Ctermeq (CnConst c1) (CnConst c2) = (c1 = c2)) ∧
  (Ctermeq t1 t2 = F)
End

Theorem Ctermeq_refl[simp]: ∀t. Ctermeq t t
Proof Induct THEN SRW_TAC [][permeq_refl]
QED

val Ctermeq_sym = Q.store_thm(
"Ctermeq_sym",
`∀t1 t2. Ctermeq t1 t2 = Ctermeq t2 t1`,
Induct THEN
Cases_on `t2` THEN SRW_TAC [][] THEN
METIS_TAC [permeq_sym]);

val Ctermeq_trans = Q.store_thm(
"Ctermeq_trans",
`∀t1 t2 t3. Ctermeq t1 t2 ∧ Ctermeq t2 t3 ⇒ Ctermeq t1 t3`,
Induct THEN Cases_on `t2` THEN Cases_on `t3` THEN SRW_TAC [][] THEN
METIS_TAC [permeq_trans]);

val Ctermeq_equiv = Q.store_thm(
"Ctermeq_equiv",
`∀t1 t2. Ctermeq t1 t2 ⇔ (Ctermeq t1 = Ctermeq t2)`,
METIS_TAC [equivalence_def,symmetric_def,reflexive_def,transitive_def,
           ALT_equivalence,Ctermeq_refl,Ctermeq_sym,Ctermeq_trans]);

val CTie_rsp = Q.store_thm(
"CTie_rsp",
`∀t1 t2 a1 a2. (a1 = a2) ∧ Ctermeq t1 t2 ⇒ Ctermeq (CTie a1 t1) (CTie a2 t2)`,
Induct THEN SRW_TAC [][]);

val CnPair_rsp = Q.store_thm(
"CnPair_rsp",
`∀t1a t1d t2a t2d. Ctermeq t1a t2a ∧ Ctermeq t1d t2d ⇒ Ctermeq (CnPair t1a t1d) (CnPair t2a t2d)`,
Induct THEN SRW_TAC [][]);

fun mk_def(t) =
let val s = (String.extract(term_to_string t,1,NONE)) in
  {def_name = s ^ "_def", fixity = NONE, fname = s, func = t}
end;

val [nterm_induction,nterm_nchotomy,ntermeq_thm]
= define_equivalence_type {
  name = "nterm",
  equiv = Ctermeq_equiv,
  defs = map mk_def [``CNom``,``CSus``,``CTie``,``CnPair``,``CnConst``],
  welldefs = [CTie_rsp,CnPair_rsp],
  old_thms = map theorem ["Cterm_induction","Cterm_nchotomy"] @ [Ctermeq_def]
};

val _ = save_thm("nterm_induction",nterm_induction);
val _ = save_thm("nterm_nchotomy",nterm_nchotomy);
val _ = RWsave_thm("ntermeq_thm",ntermeq_thm);

val (nterm_rec_rules,nterm_rec_ind,nterm_rec_cases) = Hol_reln `
  nterm_rec Nf Sf Tf Pf Cf (Nom a) (Nf a) ∧
  nterm_rec Nf Sf Tf Pf Cf (Sus p v) (Sf p v) ∧
  (nterm_rec Nf Sf Tf Pf Cf t r ⇒
   nterm_rec Nf Sf Tf Pf Cf (Tie a t) (Tf a t r)) ∧
  (nterm_rec Nf Sf Tf Pf Cf t1 r1 ∧
   nterm_rec Nf Sf Tf Pf Cf t2 r2 ⇒
    nterm_rec Nf Sf Tf Pf Cf (nPair t1 t2) (Pf t1 t2 r1 r2)) ∧
  nterm_rec Nf Sf Tf Pf Cf (nConst c) (Cf c)`;

val nterm_rec_total = Q.store_thm(
"nterm_rec_total",
`∀t. ∃r. nterm_rec Nf Sf Tf Pf Cf t r`,
HO_MATCH_MP_TAC nterm_induction THEN
METIS_TAC [nterm_rec_rules]);

val nterm_rec_unique = Q.store_thm(
"nterm_rec_unique",
`(∀p1 p2 v. p1 == p2 ⇒ (Sf p1 v = Sf p2 v)) ⇒
  ∀t r. nterm_rec Nf Sf Tf Pf Cf t r ⇒
  ∀r'. nterm_rec Nf Sf Tf Pf Cf t r' ⇒  (r' = r)`,
STRIP_TAC THEN HO_MATCH_MP_TAC nterm_rec_ind THEN
SRW_TAC [][] THENL [
  FULL_SIMP_TAC (srw_ss()) [Once nterm_rec_cases],
  FULL_SIMP_TAC (srw_ss()) [Once nterm_rec_cases],
  POP_ASSUM MP_TAC THEN
  SRW_TAC [][Once nterm_rec_cases] THEN
  METIS_TAC [],
  POP_ASSUM MP_TAC THEN
  SRW_TAC [][Once nterm_rec_cases] THEN
  METIS_TAC [],
  FULL_SIMP_TAC (srw_ss()) [Once nterm_rec_cases]
]);

val nterm_rec_exists = Q.store_thm(
"nterm_rec_exists",
`∀Nf Sf Tf Pf Cf.
 (∀p1 p2 v. p1 == p2 ⇒ (Sf p1 v = Sf p2 v)) ⇒
 ∃f. (∀a. f (Nom a) = Nf a) ∧
     (∀p v. f (Sus p v) = Sf p v) ∧
     (∀a t. f (Tie a t) = Tf a t (f t)) ∧
     (∀t1 t2. f (nPair t1 t2) = Pf t1 t2 (f t1) (f t2)) ∧
     (∀c. f (nConst c) = (Cf c))`,
REPEAT STRIP_TAC THEN Q.EXISTS_TAC `λt. @r. nterm_rec Nf Sf Tf Pf Cf t r` THEN
SRW_TAC [][] THENL [
  SELECT_ELIM_TAC THEN
  METIS_TAC [nterm_rec_unique,nterm_rec_rules],
  SELECT_ELIM_TAC THEN
  METIS_TAC [nterm_rec_unique,nterm_rec_rules],
  NTAC 2 SELECT_ELIM_TAC THEN
  SRW_TAC [][] THENL [
    METIS_TAC [nterm_rec_total],
    METIS_TAC [nterm_rec_rules],
    POP_ASSUM MP_TAC THEN
    SRW_TAC [][Once nterm_rec_cases] THEN
    METIS_TAC [nterm_rec_unique]
  ],
  NTAC 3 SELECT_ELIM_TAC THEN
  SRW_TAC [][] THENL [
    METIS_TAC [nterm_rec_total],
    METIS_TAC [nterm_rec_total],
    METIS_TAC [nterm_rec_rules],
    POP_ASSUM MP_TAC THEN
    SRW_TAC [][Once nterm_rec_cases] THEN
    METIS_TAC [nterm_rec_unique]
  ],
  SELECT_ELIM_TAC THEN
  METIS_TAC [nterm_rec_unique,nterm_rec_rules]
]);

val is_Nom_def = Define`is_Nom t = ?a. (t = Nom a)`;
val is_Sus_def = Define`is_Sus t = ?p v. (t = Sus p v)`;
val is_Tie_def = Define`is_Tie t = ?t' a. (t = Tie a t')`;
val is_nPair_def = Define`is_nPair t = ?t1 t2. (t = nPair t1 t2)`;
val _ = export_rewrites["is_Nom_def","is_Sus_def","is_Tie_def","is_nPair_def"];

val dest_Nom_def = Define `dest_Nom t = @a. t = Nom a`;
val dest_Sus_def = Define `dest_Sus t = ((@p.∃v. t = Sus p v),(@v.∃p.t = Sus
p v))`;
val dest_Tie_def = Define `dest_Tie t = @p. Tie (FST p) (SND p) = t`;
val dest_nPair_def = Define `dest_nPair t = @p. nPair (FST p) (SND p) = t`;
val dest_nConst_def = Define `dest_nConst t = @c. nConst c = t`;
val dest_Nom_thm =
RWstore_thm("dest_Nom_thm", `dest_Nom (Nom a) = a`,
SRW_TAC [][dest_Nom_def]);
val dest_Sus =
RWstore_thm("dest_Sus_thm", `dest_Sus (Sus p v) = ((@p'. p' == p),v)`,
SRW_TAC [][dest_Sus_def] THEN1
(AP_TERM_TAC THEN SRW_TAC [][FUN_EQ_THM] THEN METIS_TAC [permeq_sym]) THEN
SELECT_ELIM_TAC THEN SRW_TAC [][] THEN METIS_TAC [permeq_refl]);
val dest_Tie =
RWstore_thm("dest_Tie_thm", `dest_Tie (Tie a t) = (a,t)`,
SRW_TAC [][dest_Tie_def] THEN SELECT_ELIM_TAC THEN
REPEAT (SRW_TAC [][EXISTS_PROD,PAIR]));
val dest_nPair_thm =
RWstore_thm("dest_nPair_thm", `dest_nPair (nPair t1 t2) = (t1,t2)`,
SRW_TAC [][dest_nPair_def] THEN SELECT_ELIM_TAC THEN
REPEAT (SRW_TAC [][EXISTS_PROD,PAIR]));
val dest_nConst_thm =
RWstore_thm("dest_nConst_thm", `dest_nConst (nConst a) = a`,
SRW_TAC [][dest_nConst_def]);

val nterm_case_def = Define`
  nterm_CASE t Nf Sf Tf Pf Cf =
  if is_Nom t then Nf (dest_Nom t) else
  if is_Sus t then UNCURRY Sf (dest_Sus t) else
  if is_Tie t then UNCURRY Tf (dest_Tie t) else
  if is_nPair t then UNCURRY Pf (dest_nPair t) else Cf (dest_nConst t)`;

val nterm_case_cong = Q.store_thm(
"nterm_case_cong",
`∀t t' Nf Sf  Tf Pf Cf.
   (t = t') ∧
   (∀a. (t' = Nom a) ⇒ (Nf a = Nf' a)) ∧
   (∀p v.  (t' = Sus p v) ⇒  (Sf p v = Sf' p v)) ∧
   (∀a t.  (t' = Tie a t) ⇒  (Tf a t = Tf' a t)) ∧
   (∀t1 t2.  (t' = nPair t1 t2) ⇒ (Pf t1 t2 = Pf' t1 t2)) ∧
   (∀c.  (t' = nConst c) ⇒ (Cf c = Cf' c)) ⇒
   (nterm_CASE t Nf Sf Tf Pf Cf = nterm_CASE t' Nf' Sf' Tf' Pf' Cf')`,
REPEAT GEN_TAC THEN
Q.SPEC_THEN `t'` STRUCT_CASES_TAC nterm_nchotomy THEN
SIMP_TAC (srw_ss())
[nterm_case_def] THEN
SRW_TAC [][] THEN1
(FIRST_X_ASSUM MATCH_MP_TAC THEN SELECT_ELIM_TAC THEN
 SRW_TAC [][permeq_sym] THEN METIS_TAC [permeq_refl]) THEN
METIS_TAC [permeq_refl]);

val nterm_case_rewrites = RWstore_thm(
"nterm_case_rewrites",
`(nterm_CASE (Nom a) Nf Sf Tf Pf Cf = Nf a) ∧
 (nterm_CASE (Tie a t) Nf Sf Tf Pf Cf = Tf a t) ∧
 (nterm_CASE (nPair t1 t2) Nf Sf Tf Pf Cf = Pf t1 t2) ∧
 (nterm_CASE (nConst c) Nf Sf Tf Pf Cf = Cf c)`,
SIMP_TAC (srw_ss()) [nterm_case_def]);

val Sus_case1 = Q.store_thm(
"Sus_case1",
`nterm_CASE (Sus p v) Nf Sf Tf Pf Cf = Sf (@p'. p' == p) v`,
SRW_TAC [] [nterm_case_def]);

(* Unfortunately this theorem is wasted when using Define, since only
   Sus_case1 goes into the case theorem given to the TypeBase *)
val Sus_case2 = Q.store_thm(
"Sus_case2",
`(∀p1 p2. (p1 == p2) ⇒ (Sf p1 v = Sf p2 v)) ⇒
 (nterm_CASE (Sus p v) Nf Sf Tf Pf Cf = Sf p v)`,
SRW_TAC [] [nterm_case_def] THEN
FIRST_X_ASSUM MATCH_MP_TAC THEN
SELECT_ELIM_TAC THEN SRW_TAC [][]);

val nterm_size_def = RWnew_specification ("nterm_size_def",
  ["nterm_size"],
  nterm_rec_exists |>
  Q.INST_TYPE [`:'a`|->`:num`] |>
  Q.SPECL [
   `λa. 0`,
   `λp v. 0`,
   `λa t r. 1 + r`,
   `λt1 t2 r1 r2. 1 + r1 + r2`,
   `λc. 0`] |>
  SIMP_RULE (srw_ss()) [] |>
  GEN ``g:'b -> num`` |>
  CONV_RULE SKOLEM_CONV |>
  SIMP_RULE (srw_ss()) [FORALL_AND_THM]);

val nterm_case_eq = Q.store_thm(
  "nterm_case_eq",
  ‘(nterm_CASE n nmf sf tf pf cf = v) ⇔
     (∃a. (n = Nom a) ∧ (nmf a = v)) ∨
     (∃p w. (n = Sus p w) ∧ (sf (@p'. p' == p) w = v)) ∨
     (∃a t. (n = Tie a t) ∧ (tf a t = v)) ∨
     (∃t1 t2. (n = nPair t1 t2) ∧ (pf t1 t2 = v)) ∨
     (∃c. (n = nConst c) ∧ (cf c = v))’,
  Q.ISPEC_THEN ‘n’ STRUCT_CASES_TAC nterm_nchotomy >>
  simp[nterm_case_rewrites, Sus_case1] >> eq_tac >> rw[]
  >- (rename [‘(c == _) /\ (_ = _)’] >> qexists_tac ‘c’ >> simp[permeq_refl]) >>
  rename [‘_ (@p'. p' == c1) _ = _ (@p'. p' == c2) _’] >>
  ‘∀p. p == c2 <=> p == c1’ suffices_by simp[] >>
  metis_tac[permeq_def]);

val nterm_case_elim = Q.store_thm(
  "nterm_case_elim",
  ‘∀f. (f(nterm_CASE n nmf sf tf pf cf) ⇔
     (∃a. (n = Nom a) ∧ f(nmf a)) ∨
     (∃p w. (n = Sus p w) ∧ f(sf (@p'. p' == p) w)) ∨
     (∃a t. (n = Tie a t) ∧ f(tf a t)) ∨
     (∃t1 t2. (n = nPair t1 t2) ∧ f(pf t1 t2)) ∨
     (∃c. (n = nConst c) ∧ f(cf c)))’,
  strip_tac >>
  Q.ISPEC_THEN ‘n’ STRUCT_CASES_TAC nterm_nchotomy >>
  simp[nterm_case_rewrites, Sus_case1] >> eq_tac >> rw[]
  >- (first_x_assum $ irule_at $ Pos last >> rw[]) >>
  pop_assum mp_tac >>
  rename [‘_ (_ (@p'. p' == c1) _) ⇒ _(_ (@p'. p' == c2) _)’] >>
  ‘∀p. p == c2 <=> p == c1’ suffices_by simp[] >>
  metis_tac[permeq_def]);

local open TypeBase TypeBasePure Drule
in
val _ = export [
    mk_datatype_info {
      ax = ORIG nterm_rec_exists,
      induction = ORIG nterm_induction,
      case_def = LIST_CONJ
                 (let val (n::rest) = CONJUNCTS nterm_case_rewrites
                  in n::Sus_case1::rest end),
      case_cong = nterm_case_cong,
      case_eq = nterm_case_eq,
      case_elim = nterm_case_elim,
      nchotomy = nterm_nchotomy,
      size = SOME (``nterm_size``,ORIG nterm_size_def),
      encode = NONE,
      lift = NONE,
      one_one = NONE,
      distinct = NONE (* SOME ntermeq_thm *),
      fields = [],
      accessors = [],
      updates = [],
      destructors = [],
      recognizers = []}]
end (* local *)

val SELECT_permeq_REFL = RWstore_thm(
"SELECT_permeq_REFL",
`(@p.p==l)==l`,
SELECT_ELIM_TAC THEN SRW_TAC [][])

val Sus_eq_perms = Q.store_thm(
"Sus_eq_perms",
`p1 == p2 ⇒ (Sus p1 v = Sus p2 v)`,
SRW_TAC [][])

Definition nvars_def[simp]:
  (nvars (Sus p v) = {v}) ∧
  (nvars (Tie a t) = nvars t) ∧
  (nvars (nPair t1 t2) = nvars t1 ∪ nvars t2) ∧
  (nvars _ = {})
End

Theorem FINITE_nvars[simp]: FINITE (nvars t)
Proof Induct_on `t` THEN SRW_TAC [][]
QED

Definition nvarb_def[simp]:
  (nvarb (Sus p v) = {|v|}) ∧
  (nvarb (Tie a t) = nvarb t) ∧
  (nvarb (nPair t1 t2) = nvarb t1 + nvarb t2) ∧
  (nvarb _ = {||})
End

Theorem FINITE_nvarb[simp]: ∀t. FINITE_BAG (nvarb t)
Proof Induct THEN SRW_TAC [][]
QED

Theorem IN_nvarb_nvars[simp]:
  ∀t. BAG_IN e (nvarb t) <=> e IN nvars t
Proof Induct THEN SRW_TAC [][]
QED

val _ = export_theory ();
