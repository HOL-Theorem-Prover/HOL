open HolKernel bossLib fmaptreeTheory finite_mapTheory pred_setTheory lcsymtacs
val _ = new_theory"type_Cv"

val _ = Parse.overload_on("num_to_s0",``GENLIST (K (CHR 0))``)
val _ = Parse.overload_on("s0_to_num",``STRLEN``)

val b = ``:string``
val a = ``:lit +
num +
string list # α +
string list # (string list # α) list # string``
val Cv0 = ``:(^b,^a) fmaptree``
val _ = type_abbrev("Cv0",Cv0)
val Cvwf_def = new_specification("Cvwf_def",["Cvwf"],
fmtree_Axiom
|> Q.ISPEC
`λ^(mk_var("i",a)) ^(mk_var("fm",``:^b |-> (^b,^a) fmaptree``)) ^(mk_var("res",``:(^b,bool) fmap``)). (∀x. x ∈ FRANGE res ⇒ x) ∧
case i of
  | (INL l) => (fm = FEMPTY)
  | (INR (INL n)) => ∃vs. (fm = FUN_FMAP (combin$C EL vs o s0_to_num) (IMAGE num_to_s0 (count (LENGTH vs))))
  | (INR (INR (INL (xs,b)))) => T
  | (INR (INR (INR (ns,defs,d)))) => T`)
val Cv1s_exist = new_type_definition("Cv1",
prove(
``∃v. Cvwf v``,
qexists_tac`FTNode (INL (Bool F)) FEMPTY` >>
rw[Cvwf_def]))

val Cv1_bij_thm = define_new_type_bijections {
  ABS="toCv1", REP="fromCv1", name = "Cv1_bij_thm", tyax = Cv1s_exist}

val CLitv_def = Define`
  CLitv l = toCv1 (FTNode (INL l) FEMPTY)`
val CConv_def = Define`
  CConv n vs = toCv1
    (FTNode (INR (INL n))
            (fromCv1 o_f FUN_FMAP (combin$C EL vs o s0_to_num) (IMAGE num_to_s0 (count (LENGTH vs)))))`
val CClosure_def = Define`
  CClosure env xs b = toCv1
    (FTNode (INR (INR (INL (xs,b))))
            (fromCv1 o_f env))`
val CRecClos_def = Define`
  CRecClos env ns defs d = toCv1
    (FTNode (INR (INR (INR (ns,defs,d))))
            (fromCv1 o_f env))`

val num_to_s0_inj = store_thm(
"num_to_s0_inj",
``∀x y. (num_to_s0 x = num_to_s0 y) = (x = y)``,
rpt gen_tac >>
reverse EQ_TAC >- rw[] >>
rw[listTheory.LIST_EQ_REWRITE])

val toCv1_thm = store_thm(
"toCv1_thm",
``Cvwf (FTNode i fm) ⇒
  (toCv1 (FTNode i fm) = case i of
   | INL l => CLitv l
   | INR (INL n) => CConv n (MAP toCv1 (GENLIST (FAPPLY fm o num_to_s0) (CARD (FDOM fm))))
   | INR (INR (INL (xs,b))) => CClosure (toCv1 o_f fm) xs b
   | INR (INR (INR (ns,defs,n))) => CRecClos (toCv1 o_f fm) ns defs n)``,
rw[Cvwf_def] >>
BasicProvers.EVERY_CASE_TAC >- (
  rw[CLitv_def] )
>- (
  rw[CConv_def] >>
  AP_TERM_TAC >>
  AP_TERM_TAC >>
  fs[FUN_FMAP_DEF,CARD_INJ_IMAGE,num_to_s0_inj] >>
  ONCE_REWRITE_TAC[GSYM fmap_EQ_THM] >>
  conj_tac >- rw[] >>
  gen_tac >>
  simp_tac std_ss [FUN_FMAP_DEF,IMAGE_FINITE,FINITE_COUNT] >>
  strip_tac >>
  asm_simp_tac std_ss [o_f_FAPPLY,FUN_FMAP_DEF,IMAGE_FINITE,FINITE_COUNT] >>
  fs[rich_listTheory.EL_MAP] >> rw[] >>
  qmatch_assum_rename_tac `x < LENGTH vs`[] >>
  `num_to_s0 x ∈ IMAGE num_to_s0 (count (LENGTH vs))` by (rw[] >> PROVE_TAC[]) >>
  rw[FUN_FMAP_DEF] >>
  match_mp_tac EQ_SYM >>
  rw[GSYM (CONJUNCT2 Cv1_bij_thm)] >>
  first_x_assum match_mp_tac >>
  rw[FRANGE_DEF] >>
  qexists_tac `num_to_s0 x` >>
  rw[FUN_FMAP_DEF] >>
  PROVE_TAC[])
>- (
  rw[CClosure_def] >>
  AP_TERM_TAC >>
  AP_TERM_TAC >>
  ONCE_REWRITE_TAC[GSYM fmap_EQ_THM] >>
  rw[] >>
  match_mp_tac EQ_SYM >>
  rw[GSYM (CONJUNCT2 Cv1_bij_thm)] >>
  first_x_assum match_mp_tac >>
  rw[FRANGE_DEF] >>
  qexists_tac `x` >>
  rw[] ) >>
rw[CRecClos_def] >>
AP_TERM_TAC >>
AP_TERM_TAC >>
ONCE_REWRITE_TAC[GSYM fmap_EQ_THM] >>
rw[] >>
match_mp_tac EQ_SYM >>
rw[GSYM (CONJUNCT2 Cv1_bij_thm)] >>
first_x_assum match_mp_tac >>
rw[FRANGE_DEF] >>
qexists_tac `x` >>
rw[] )

val Cvwf_all_Cv1 = store_thm(
"Cvwf_all_Cv1",
``(∀x. Cvwf x ⇒ P (toCv1 x)) ⇒ (∀v. P v)``,
metis_tac[Cv1_bij_thm])

val Cvwf_thm = LIST_CONJ [
  SIMP_RULE (srw_ss())[](Q.SPEC`INL l`Cvwf_def),
  SIMP_RULE (srw_ss())[](Q.SPEC`INR (INL n)`Cvwf_def),
  SIMP_RULE (srw_ss())[](Q.SPEC`INR (INR (INL (xs,b)))`Cvwf_def),
  SIMP_RULE (srw_ss())[](Q.SPEC`INR (INR (INR (ns,defs,n)))`Cvwf_def)
]

val Cv1_induction = store_thm(
"Cv1_induction",
``∀P0 P1 P2.
(∀l. P0 (CLitv l)) ∧
(∀vs. P2 vs ⇒ ∀n. P0 (CConv n vs)) ∧
(∀env. P1 env ⇒ ∀xs b. P0 (CClosure env xs b)) ∧
(∀env. P1 env ⇒ ∀ns defs d. P0 (CRecClos env ns defs d)) ∧
(* (∀env. (∀v. v ∈ FRANGE env ⇒ P0 v) ⇒ P1 env) ∧ *)
(P1 FEMPTY) ∧
(∀s v env. P0 v ∧ P1 env ⇒ P1 (env |+ (s,v))) ∧
(P2 []) ∧
(∀v vs. P0 v ∧ P2 vs ⇒ P2 (v::vs))
⇒
(∀v. P0 v) ∧ (∀env. P1 env) ∧ (∀vs. P2 vs)``,
rpt gen_tac >> strip_tac >>
reverse conj_asm1_tac >- (
  conj_tac >- (
    ho_match_mp_tac fmap_INDUCT >>
    rw[] ) >>
  Induct >> rw[]) >>
match_mp_tac Cvwf_all_Cv1 >>
ho_match_mp_tac ft_ind >>
rpt strip_tac >>
rw[toCv1_thm] >>
BasicProvers.EVERY_CASE_TAC >- rw[] >>
first_x_assum match_mp_tac >- (
  `∀vs. EVERY P0 vs ⇒ P2 vs` by (Induct >> rw[]) >>
  pop_assum match_mp_tac >>
  rw[listTheory.EVERY_MAP,listTheory.EVERY_MEM,listTheory.MEM_GENLIST] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  qpat_assum `Cvwf X` mp_tac >>
  REWRITE_TAC [Cvwf_thm] >>
  strip_tac >>
  conj_tac >- (
    pop_assum SUBST_ALL_TAC >>
    qpat_assum `m < X` mp_tac >>
    simp_tac std_ss [FUN_FMAP_DEF,IMAGE_FINITE,FINITE_COUNT] >>
    simp_tac std_ss [IN_IMAGE,IN_COUNT] >>
    simp_tac std_ss [CARD_INJ_IMAGE,num_to_s0_inj,FINITE_COUNT,CARD_COUNT]) >>
  first_x_assum match_mp_tac >>
  rw[FRANGE_DEF] >>
  qexists_tac `num_to_s0 m` >>
  fs[FUN_FMAP_DEF,CARD_INJ_IMAGE,num_to_s0_inj] ) >>
`∀env. (∀v. v ∈ FRANGE env ⇒ P0 v) ⇒ P1 env` by (
  ho_match_mp_tac fmap_INDUCT >>
  rw[] >>
  first_x_assum match_mp_tac >>
  conj_tac >> first_x_assum match_mp_tac >>
  fs[FRANGE_DEF,DOMSUB_FAPPLY_THM] >>
  PROVE_TAC[] ) >>
pop_assum match_mp_tac >>
rw[FRANGE_DEF] >>
rw[o_f_FAPPLY] >>
first_x_assum (qspec_then `x` (match_mp_tac o MP_CANON)) >>
fs[Cvwf_thm] >>
first_x_assum match_mp_tac >>
rw[FRANGE_DEF] >>
qexists_tac `x` >> rw[]
(*
first_assum match_mp_tac >>
fs[Cvwf_thm] >>
ONCE_REWRITE_TAC[FRANGE_DEF] >>
simp_tac(srw_ss())[] >>
simp_tac(srw_ss()++boolSimps.DNF_ss)[] >>
rpt strip_tac >>
first_x_assum (qspec_then `x` (match_mp_tac o MP_CANON)) >>
rw[] >>
first_x_assum match_mp_tac >>
rw[FRANGE_DEF] >>
qexists_tac `x` >> rw[]
*)
)

val Cv1_nice_ind =
Cv1_induction
|> Q.SPECL [`P`,`FEVERY (P o SND)`,`EVERY P`]
|> SIMP_RULE (srw_ss()) [FEVERY_FEMPTY,FEVERY_STRENGTHEN_THM]
|> UNDISCH_ALL
|> CONJUNCT1
|> DISCH_ALL
|> Q.GEN `P`

val Cvwf_fromCv1 = store_thm(
"Cvwf_fromCv1",
``∀x. Cvwf (fromCv1 x)``,
METIS_TAC[Cv1_bij_thm])
val _ = export_rewrites["Cvwf_fromCv1"]

val Cvwf_o_fromCv1 = store_thm(
"Cvwf_o_fromCv1",
``Cvwf o fromCv1 = K T``,
rw[FUN_EQ_THM])
val _ = export_rewrites["Cvwf_o_fromCv1"]

val Cvwf_constructors = store_thm(
"Cvwf_constructors",
``(Cvwf ^(rand(rhs(concl(SPEC_ALL CLitv_def))))) ∧
  (Cvwf ^(rand(rhs(concl(SPEC_ALL CConv_def))))) ∧
  (Cvwf ^(rand(rhs(concl(SPEC_ALL CClosure_def))))) ∧
  (Cvwf ^(rand(rhs(concl(SPEC_ALL CRecClos_def)))))``,
rw[Cvwf_def,FRANGE_DEF] >>
rw[o_f_FAPPLY] >- (
  qmatch_abbrev_tac `(K T o_f fm) ' x` >>
  `x ∈ FDOM fm` by (
    unabbrev_all_tac >> rw[] >> PROVE_TAC[] ) >>
  rw[o_f_FAPPLY] ) >>
qexists_tac `MAP fromCv1 vs` >>
rw[GSYM fmap_EQ_THM] >>
qmatch_abbrev_tac `X = FUN_FMAP x y ' z` >>
`z ∈ y` by (
  unabbrev_all_tac >> rw[] >> PROVE_TAC[] ) >>
unabbrev_all_tac >>
rw[FUN_FMAP_DEF,listTheory.EL_MAP] )
val _ = export_rewrites["Cvwf_constructors"]

val Cv1_11 = store_thm(
"Cv1_11",``
(∀l1 l2.
  (CLitv l1 = CLitv l2) = (l1 = l2)) ∧
(∀m1 vs1 m2 vs2.
  (CConv m1 vs1 = CConv m2 vs2) = ((m1 = m2) ∧ (vs1 = vs2))) ∧
(∀env1 xs1 b1 env2 xs2 b2.
  (CClosure env1 xs1 b1 = CClosure env2 xs2 b2) =
  ((env1 = env2) ∧ (xs1 = xs2) ∧ (b1 = b2))) ∧
(∀env1 ns1 defs1 n1 env2 ns2 defs2 n2.
  (CRecClos env1 ns1 defs1 n1 = CRecClos env2 ns2 defs2 n2) =
  ((env1 = env2) ∧ (ns1 = ns2) ∧ (defs1 = defs2) ∧ (n1 = n2)))``,
conj_tac >- (
  rw[CLitv_def] >>
  reverse EQ_TAC >- rw[] >>
  strip_tac >>
  qmatch_assum_abbrev_tac `toCv1 r1 = toCv1 r2` >>
  `Cvwf r1 ∧ Cvwf r2` by (
    rw[Abbr`r1`,Abbr`r2`] ) >>
  `r1 = r2` by PROVE_TAC[Cv1_bij_thm] >>
  unabbrev_all_tac >>
  fs[] ) >>
conj_tac >- (
  rw[CConv_def] >>
  reverse EQ_TAC >- rw[] >>
  strip_tac >>
  qmatch_assum_abbrev_tac `toCv1 r1 = toCv1 r2` >>
  `Cvwf r1 ∧ Cvwf r2` by (
    rw[Abbr`r1`,Abbr`r2`]  ) >>
  `r1 = r2` by PROVE_TAC[Cv1_bij_thm] >>
  unabbrev_all_tac >>
  fsrw_tac[boolSimps.DNF_ss][GSYM fmap_EQ_THM] >>
  fs[IMAGE_11,num_to_s0_inj] >>
  rw[listTheory.LIST_EQ_REWRITE] >>
  first_x_assum (qspec_then `x` mp_tac) >>
  `num_to_s0 x ∈ IMAGE num_to_s0 (count (LENGTH vs2))` by (
    rw[] >> PROVE_TAC[] ) >>
  rw[FUN_FMAP_DEF] >>
  PROVE_TAC[Cv1_bij_thm] ) >>
conj_tac >- (
  rw[CClosure_def] >>
  reverse EQ_TAC >- rw[] >>
  strip_tac >>
  qmatch_assum_abbrev_tac `toCv1 r1 = toCv1 r2` >>
  `Cvwf r1 ∧ Cvwf r2` by rw[Abbr`r1`,Abbr`r2`] >>
  `r1 = r2` by PROVE_TAC[Cv1_bij_thm] >>
  unabbrev_all_tac >>
  fsrw_tac[boolSimps.DNF_ss][GSYM fmap_EQ_THM] >>
  pop_assum mp_tac >> rw[] >>
  PROVE_TAC[Cv1_bij_thm] ) >>
rw[CRecClos_def] >>
reverse EQ_TAC >- rw[] >>
strip_tac >>
qmatch_assum_abbrev_tac `toCv1 r1 = toCv1 r2` >>
`Cvwf r1 ∧ Cvwf r2` by rw[Abbr`r1`,Abbr`r2`] >>
`r1 = r2` by PROVE_TAC[Cv1_bij_thm] >>
unabbrev_all_tac >>
fsrw_tac[boolSimps.DNF_ss][GSYM fmap_EQ_THM] >>
pop_assum mp_tac >> rw[] >>
PROVE_TAC[Cv1_bij_thm] )
val _ = export_rewrites["Cv1_11"]

val Cv1_distinct = store_thm(
"Cv1_distinct",
``(∀l m vs. CLitv l ≠ CConv m vs) ∧
  (∀l env xs b. CLitv l ≠ CClosure env xs b) ∧
  (∀l env ns defs n. CLitv l ≠ CRecClos env ns defs n) ∧
  (∀m vs env xs b. CConv m vs ≠ CClosure env xs b) ∧
  (∀m vs env ns defs n. CConv m vs ≠ CRecClos env ns defs n) ∧
  (∀env xs b envr ns defs n. CClosure env xs b ≠ CRecClos envr ns defs n)``,
rw[CLitv_def,CConv_def,CClosure_def,CRecClos_def] >>
qmatch_abbrev_tac `toCv1 r1 ≠ toCv1 r2` >>
(qsuff_tac `Cvwf r1 ∧ Cvwf r2 ∧ r1 ≠ r2` >- PROVE_TAC[Cv1_bij_thm]) >>
unabbrev_all_tac >> fs[])

val Cv1_nchotomy = store_thm(
"Cv1_nchotomy",
``∀Cv1.
  (∃l. Cv1 = CLitv l) ∨
  (∃m vs. Cv1 = CConv m vs) ∨
  (∃env xs b. Cv1 = CClosure env xs b) ∨
  (∃env ns defs n. Cv1 = CRecClos env ns defs n)``,
ho_match_mp_tac Cv1_nice_ind >> rw[])

val Cv1_Axiom = store_thm(
"Cv1_Axiom",
``∀f0 f1 f2 f3 f4 f5 f6 f7.
∃fn0 fn1 fn2.
(∀l. fn0 (CLitv l) = f0 l) ∧
(∀m vs. fn0 (CConv m vs) = f1 m vs (fn1 vs)) ∧
(∀env xs b. fn0 (CClosure env xs b) = f2 env xs b (fn2 env)) ∧
(∀env ns defs d. fn0 (CRecClos env ns defs d) = f3 env ns defs d (fn2 env)) ∧
(fn1 [] = f4) ∧
(∀v vs. fn1 (v::vs) = f5 v vs (fn0 v) (fn1 vs)) ∧
(∀env. fn2 env = f6 env (f7 o_f env))``,
rw[] >>


val Cv1_case_def = Prim_rec.define_case_constant Cv1_Axiom
val Cv1_case_cong = Prim_rec.case_cong_thm Cv1_nchotomy Cv1_case_def

TypeBasePure.gen_datatype_info
{ax=Cv1_Axiom, ind=Cv1_induction0, case_defs=Prim_rec.define_case_constant Cv1_Axiom}

(*
type Cv =
  | CLitv of lit
  | CConv of num * Cv list
  | CClosure of (string,Cv) alist * string list * Cexp
  | CRecClos of (string,Cv) alist * string list * (string list * Cexp) list * string
*)
