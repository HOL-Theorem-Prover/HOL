open HolKernel boolLib Parse

open ncLib bossLib metisLib BasicProvers boolSimps

val SUBSET_DEF = pred_setTheory.SUBSET_DEF

(*

   fsubty ::= TyVar of string | Top | Fun of fsubty => fsubty
          |   ForallTy of string => fsubty => fsubty

   where the string in ForallTy binds in the second fsubty argument, but
   not the first

   Inductively characterise a subset of the lambda calculus terms that
   can stand in for these types.  The encoding is

     CON T                    -->  Top
     CON F @@ t @@ LAM v t'   -->  ForallTy v t t'
     VAR s                    -->  TyVar s
     t @@ u                   -->  Fun t u

*)

val _ = new_theory "fsubtypes"

val (fsubrep_rules, fsubrep_ind, fsubrep_cases) = Hol_reln`
  fsubrep (CON T) /\
  (!v t t'. fsubrep t /\ fsubrep t' ==> fsubrep (CON F @@ t @@ LAM v t')) /\
  (!s. fsubrep (VAR s)) /\
  (!t u. fsubrep t /\ fsubrep u ==> fsubrep (t @@ u))
`;

val strong_fsubrep_ind = save_thm(
  "strong_fsubrep_ind",
  IndDefRules.derive_strong_induction (CONJUNCTS fsubrep_rules,
                                       fsubrep_ind));

(* because this is not obviously non-overlapping, we need to prove that
   certain patterns aren't in fsubrep by induction *)

val lam_not_fsubrep0 = prove(
  ``!t0. fsubrep t0 ==> !v t. (t0 = LAM v t) ==> F``,
  HO_MATCH_MP_TAC fsubrep_ind THEN SRW_TAC [][]);
val lam_not_fsubrep = save_thm(
  "lam_not_fsubrep",
  SIMP_RULE (srw_ss() ++ DNF_ss) [] lam_not_fsubrep0)
val _ = export_rewrites ["lam_not_fsubrep"]

val CONF_not_fsubrep = store_thm(
  "CONF_not_fsubrep",
  ``~(fsubrep (CON F))``,
  ONCE_REWRITE_TAC [fsubrep_cases] THEN SRW_TAC [][]);
val _ = export_rewrites ["CONF_not_fsubrep"]


val fsubty_def = new_type_definition (
  "fsubty",
  prove(``?x. fsubrep x``, Q.EXISTS_TAC `CON T` THEN
                           SRW_TAC [][fsubrep_rules])
);

val bijections_exist =
    define_new_type_bijections {name = "bijections_exist",
                                ABS = "term2fsubty",
                                REP = "fsubty2term",
                                tyax = fsubty_def};

(* obvious facts about the bijections *)
val fsubty2term_11 = store_thm(
  "fsubty2term_11",
  ``(fsubty2term ty1 = fsubty2term ty2) = (ty1 = ty2)``,
  SRW_TAC [][EQ_IMP_THM] THEN
  METIS_TAC [bijections_exist]);
val _ = export_rewrites ["fsubty2term_11"]

val term2fsubty_11 = store_thm(
  "term2fsubty_11",
  ``fsubrep t1 /\ fsubrep t2 ==>
    ((term2fsubty t1 = term2fsubty t2) = (t1 = t2))``,
  SRW_TAC [][EQ_IMP_THM] THEN METIS_TAC [bijections_exist]);

val fsubrep_fsubty2term = store_thm(
  "fsubrep_fsubty2term",
  ``fsubrep (fsubty2term ty1)``,
  METIS_TAC [bijections_exist]);
val _ = export_rewrites ["fsubrep_fsubty2term"]


(* define constructors *)
val Top_def = Define`Top = term2fsubty (CON T)`;
val TyVar_def = Define`TyVar s = term2fsubty (VAR s)`;
val Fun_def = Define`
  Fun ty1 ty2 = term2fsubty (fsubty2term ty1 @@ fsubty2term ty2)
`;
val ForallTy_def = Define`
  ForallTy v boundty ty =
    term2fsubty (CON F @@ fsubty2term boundty @@ LAM v (fsubty2term ty))
`;

(* prove injectivity for the non-binder constructors *)
val Fun_11 = store_thm(
  "Fun_11",
  ``(Fun ty1 ty2 = Fun ty3 ty4) = (ty1 = ty3) /\ (ty2 = ty4)``,
  SIMP_TAC (srw_ss()) [Fun_def, EQ_IMP_THM, fsubrep_rules, term2fsubty_11]);
val _ = export_rewrites ["Fun_11"]

val TyVar_11 = store_thm(
  "TyVar_11",
  ``(TyVar s1 = TyVar s2) = (s1 = s2)``,
  SIMP_TAC (srw_ss()) [TyVar_def, fsubrep_rules, term2fsubty_11]);
val _ = export_rewrites ["TyVar_11"]

(* prove distinctness *)
val fsubty_distinct = store_thm(
  "fsubty_distinct",
  ``~(Top = TyVar s) /\ ~(Top = Fun ty1 ty2) /\ ~(Top = ForallTy v bnd ty) /\
    ~(TyVar s = Fun ty1 ty2) /\ ~(TyVar s = ForallTy v bnd ty) /\
    ~(Fun ty1 ty2 = ForallTy v bnd ty)``,
  SRW_TAC [][Top_def, TyVar_def, Fun_def, ForallTy_def,
             fsubrep_rules, term2fsubty_11] THEN
  DISJ2_TAC THEN STRIP_TAC THEN
  POP_ASSUM (MP_TAC o Q.AP_TERM `fsubrep`) THEN
  SRW_TAC [][]);
val _ = export_rewrites ["fsubty_distinct"]

val forall_fsubty = prove(
  ``(!ty. P ty) = (!t. fsubrep t ==> P (term2fsubty t))``,
  SRW_TAC [][EQ_IMP_THM] THEN
  `?t. (ty = term2fsubty t) /\ fsubrep t`
       by METIS_TAC [bijections_exist] THEN
  METIS_TAC []);

val rep_abs_lemma = prove(
  ``fsubrep t ==> (fsubty2term (term2fsubty t) = t)``,
  METIS_TAC [bijections_exist])

(* induction principle *)
val fsubty_ind = store_thm(
  "fsubty_ind",
  ``!P.
        P Top /\
        (!ty1 ty2. P ty1 /\ P ty2 ==> P (Fun ty1 ty2)) /\
        (!s. P (TyVar s)) /\
        (!v bnd ty. P bnd /\ P ty ==> P (ForallTy v bnd ty)) ==>
        !ty. P ty``,
  SIMP_TAC (srw_ss())
           [forall_fsubty, Top_def, TyVar_def, Fun_def, ForallTy_def,
            rep_abs_lemma] THEN
  GEN_TAC THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC strong_fsubrep_ind THEN
  METIS_TAC []);

(* definition of swap *)
val fswap_def = Define`
  fswap x y ty = term2fsubty (swap x y (fsubty2term ty))
`;

val fsubrep_swap = store_thm(
  "fsubrep_swap",
  ``!t. fsubrep t ==> !x y. fsubrep (swap x y t)``,
  HO_MATCH_MP_TAC fsubrep_ind THEN
  SRW_TAC [][swapTheory.swap_thm, fsubrep_rules]);

val fswap_thm = store_thm(
  "fswap_thm",
  ``(!s. fswap x y (TyVar s) = TyVar (swapstr x y s)) /\
    (!ty1 ty2. fswap x y (Fun ty1 ty2) =
                 Fun (fswap x y ty1) (fswap x y ty2)) /\
    (fswap x y Top = Top) /\
    (!v bnd ty. fswap x y (ForallTy v bnd ty) =
       ForallTy (swapstr x y v) (fswap x y bnd) (fswap x y ty))``,
  SRW_TAC [][fswap_def, Top_def, ForallTy_def, Fun_def, TyVar_def,
             rep_abs_lemma, fsubrep_rules, swapTheory.swap_thm,
             fsubrep_swap]);

val fswap_inv = store_thm(
  "fswap_inv",
  ``!ty x y. fswap x y (fswap x y ty) = ty``,
  HO_MATCH_MP_TAC fsubty_ind THEN SRW_TAC [][fswap_thm]);
val _ = export_rewrites ["fswap_inv"]

val fswap_id = store_thm(
  "fswap_id",
  ``fswap x x ty = ty``,
  SRW_TAC [][fswap_def, bijections_exist]);
val _ = export_rewrites ["fswap_id"]

val fswap_comm = store_thm(
  "fswap_comm",
  ``fswap y x = fswap x y``,
  SRW_TAC [][FUN_EQ_THM, fswap_def, swapTheory.swap_comm]);

(* define swap over contexts *)
val ctxtswap_def = Define`
  (ctxtswap x y [] = []) /\
  (ctxtswap x y (h::t) = (swapstr x y (FST h), fswap x y (SND h)) ::
                         ctxtswap x y t)
`;
val _ = export_rewrites ["ctxtswap_def"]

val ctxtswap_inv = store_thm(
  "ctxtswap_inv",
  ``!G x y. ctxtswap x y (ctxtswap x y G) = G``,
  Induct THEN SRW_TAC [][]);
val _ = export_rewrites ["ctxtswap_inv"]

val ctxtswap_id = store_thm(
  "ctxtswap_id",
  ``!G x y. ctxtswap x x G = G``,
  Induct THEN SRW_TAC [][ctxtswap_def]);
val _ = export_rewrites ["ctxtswap_id"]

val MEM_ctxtswap = store_thm(
  "MEM_ctxtswap",
  ``!G x y v ty. MEM (v,ty) (ctxtswap x y G) =
                 MEM (swapstr x y v, fswap x y ty) G``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  METIS_TAC [fswap_inv]);
val _ = export_rewrites ["MEM_ctxtswap"]

val cdom_def = Define`
  (cdom ([]: (string # fsubty) list)  = {}) /\
  (cdom (h::t) = FST h INSERT cdom t)
`;
val _ = export_rewrites ["cdom_def"]

val FINITE_cdom = store_thm(
  "FINITE_cdom",
  ``!G. FINITE (cdom G)``,
  Induct THEN SRW_TAC [][]);
val _ = export_rewrites ["FINITE_cdom"]

val cdom_MEM = store_thm(
  "cdom_MEM",
  ``x IN cdom G = ?ty. MEM (x,ty) G``,
  Induct_on `G` THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  METIS_TAC []);

(* define fv for types *)
val ftyFV_def = Define`
  ftyFV ty = FV (fsubty2term ty)
`;

val ftyFV_thm = store_thm(
  "ftyFV_thm",
  ``(ftyFV Top = {}) /\
    (ftyFV (Fun ty1 ty2) = ftyFV ty1 UNION ftyFV ty2) /\
    (ftyFV (TyVar s) = {s}) /\
    (ftyFV (ForallTy v bnd ty) = ftyFV bnd UNION (ftyFV ty DELETE v))``,
  SRW_TAC [][ftyFV_def, Top_def, Fun_def, ForallTy_def, TyVar_def,
             rep_abs_lemma, fsubrep_rules]);
val _ = export_rewrites ["ftyFV_thm"]

(* the following is not really an injectivity result, but it seems the best
   possible for ForallTy *)
val ForallTy_11 = store_thm(
  "ForallTy_11",
  ``(ForallTy v1 bnd1 bod1 = ForallTy v2 bnd2 bod2) =
      (bnd1 = bnd2) /\ ((v1 = v2) \/ ~(v1 IN ftyFV bod2)) /\
      (bod1 = fswap v1 v2 bod2)``,
  SRW_TAC [][ftyFV_def, ftyFV_thm, fswap_def, ForallTy_def,
             term2fsubty_11, fsubrep_rules, swapTheory.LAM_INJ_swap,
             EQ_IMP_THM] THEN
  ASM_SIMP_TAC (srw_ss()) [] THENL [
    FIRST_X_ASSUM (MP_TAC o Q.AP_TERM `term2fsubty`) THEN
    SRW_TAC [][bijections_exist],
    FIRST_X_ASSUM (MP_TAC o Q.AP_TERM `term2fsubty`) THEN
    SRW_TAC [][bijections_exist],
    SRW_TAC [][bijections_exist],
    SRW_TAC [][rep_abs_lemma, fsubrep_fsubty2term, fsubrep_swap]
  ]);

val ForallTy_injectivity_lemma1 = store_thm(
  "ForallTy_injectivity_lemma1",
  ``(ForallTy x bnd1 ty1 = ForallTy y bnd2 ty2) ==>
    (bnd1 = bnd2) /\ (ty2 = fswap x y ty1)``,
  METIS_TAC [ForallTy_11, fswap_inv]);

val ForallTy_INJ_ALPHA_FV = store_thm(
  "ForallTy_INJ_ALPHA_FV",
  ``(ForallTy x bnd ty1 = ForallTy y bnd ty2) /\ ~(x = y) ==>
    ~(x IN ftyFV ty2) /\ ~(y IN ftyFV ty1)``,
  METIS_TAC [ForallTy_11]);

val ForallTy_ALPHA = store_thm(
  "ForallTy_ALPHA",
  ``~(u IN ftyFV ty) ==>
    (ForallTy u bnd (fswap u v ty) = ForallTy v bnd ty)``,
  METIS_TAC [ForallTy_11]);

val fswap_fresh = store_thm(
  "fswap_fresh",
  ``!ty x y. ~(x IN ftyFV ty) /\ ~(y IN ftyFV ty) ==>
             (fswap x y ty = ty)``,
  SRW_TAC [][fswap_def, ftyFV_def, swapTheory.swap_identity,
             bijections_exist]);

val swapset_DELETE = store_thm(
  "swapset_DELETE",
  ``swapset x y (s1 DELETE s) = swapset x y s1 DELETE swapstr x y s``,
  SRW_TAC [][swapTheory.swapset_def, pred_setTheory.EXTENSION]);

val swapset_SUBSET = store_thm(
  "swapset_SUBSET",
  ``s1 SUBSET swapset x y s2 = swapset x y s1 SUBSET s2``,
  SRW_TAC [][swapTheory.swapset_def, SUBSET_DEF] THEN
  METIS_TAC [swapTheory.swapstr_inverse]);
val _ = export_rewrites ["swapset_SUBSET"]

val ftyFV_fswap = store_thm(
  "ftyFV_fswap",
  ``!ty x y. ftyFV (fswap x y ty) = swapset x y (ftyFV ty)``,
  HO_MATCH_MP_TAC fsubty_ind THEN
  SRW_TAC [][fswap_thm, swapTheory.swapset_UNION, swapset_DELETE]);
val _ = export_rewrites ["ftyFV_fswap"]

val ftyFV_FINITE = store_thm(
  "ftyFV_FINITE",
  ``!ty. FINITE (ftyFV ty)``,
  HO_MATCH_MP_TAC fsubty_ind THEN
  SRW_TAC [][]);
val _ = export_rewrites ["ftyFV_FINITE"]

(* define FV for ctxts *)
val ctxtFV_def = Define`
  (ctxtFV [] = {}) /\
  (ctxtFV (h::t) = {FST h} UNION ftyFV (SND h) UNION ctxtFV t)
`;
val _ = export_rewrites ["ctxtFV_def"]

val ctxtFV_ctxtswap = store_thm(
  "ctxtFV_ctxtswap",
  ``!G x y. ctxtFV (ctxtswap x y G) = swapset x y (ctxtFV G)``,
  Induct THEN SRW_TAC [][swapTheory.swapset_UNION]);
val _ = export_rewrites ["ctxtFV_ctxtswap"]

val ctxtFV_FINITE = store_thm(
  "ctxtFV_FINITE",
  ``!G. FINITE (ctxtFV G)``,
  Induct THEN SRW_TAC [][]);
val _ = export_rewrites ["ctxtFV_FINITE"]

val cdom_SUBSET_ctxtFV = store_thm(
  "cdom_SUBSET_ctxtFV",
  ``!G. cdom G SUBSET ctxtFV G``,
  Induct THEN
  FULL_SIMP_TAC (srw_ss()) [cdom_def, SUBSET_DEF] THEN
  METIS_TAC []);

val cdom_ctxtswap = store_thm(
  "cdom_ctxtswap",
  ``!G x y. cdom (ctxtswap x y G) = swapset x y (cdom G)``,
  Induct THEN SRW_TAC[][]);
val _ = export_rewrites ["cdom_ctxtswap"]

val ctxtswap_fresh = store_thm(
  "ctxtswap_fresh",
  ``!G x y.
       ~(x IN ctxtFV G) /\ ~(y IN ctxtFV G) ==>
       (ctxtswap x y G = G)``,
  Induct THEN SRW_TAC [][fswap_fresh]);

(* wfctxt implements the restrictions defined on pp393-4 *)
val wfctxt_def = Define`
  (wfctxt [] = T) /\
  (wfctxt ((x,ty) :: t) = ~(x IN cdom t) /\
                          ftyFV ty SUBSET cdom t /\
                          wfctxt t)
`;
val _ = export_rewrites ["wfctxt_def"]

val wfctxt_swap = store_thm(
  "wfctxt_swap",
  ``!G x y. wfctxt (ctxtswap x y G) = wfctxt G``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);
val _ = export_rewrites ["wfctxt_swap"]

val wfctxt_ctxtFV_cdom = store_thm(
  "wfctxt_ctxtFV_cdom",
  ``!G. wfctxt G ==> (ctxtFV G = cdom G)``,
  SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION] THEN
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, SUBSET_DEF] THEN
  METIS_TAC []);

val wfctxt_MEM = store_thm(
  "wfctxt_MEM",
  ``!G. wfctxt G /\ MEM (x,ty) G ==>
        x IN cdom G /\ !y. y IN ftyFV ty ==> y IN cdom G``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD,
                                       SUBSET_DEF] THEN
  METIS_TAC []);

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 425),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "|-", BreakSpace(1, 0),
                                 BeginFinalBlock(PP.INCONSISTENT, 2),
                                 TM, HardSpace 1, TOK "<:", BreakSpace(1,0)],
                  term_name = "fsubtyping"}

val (fsubtyping_rules, fsubtyping_ind, fsubtyping_cases) = Hol_reln`
  (!Gamma ty. wfctxt Gamma /\ ftyFV ty SUBSET cdom Gamma ==>
              Gamma |- ty <: ty) /\
  (!Gamma ty1 ty2 ty3. Gamma |- ty1 <: ty2 /\
                       Gamma |- ty2 <: ty3 ==>
                       Gamma |- ty1 <: ty3) /\
  (!Gamma ty. wfctxt Gamma /\ ftyFV ty SUBSET cdom Gamma ==>
              Gamma |- ty <: Top) /\
  (!Gamma x ty. wfctxt Gamma /\ MEM (x, ty) Gamma ==>
                Gamma |- TyVar x <: ty) /\
  (!Gamma s1 t1 s2 t2.
          Gamma |- t1 <: s1 /\ Gamma |- s2 <: t2 ==>
          Gamma |- Fun s1 s2 <: Fun t1 t2) /\
  (!Gamma x u1 s2 t2.
          ~(x IN ftyFV u1) /\ ~(x IN cdom Gamma) /\
          ftyFV u1 SUBSET cdom Gamma /\
          ((x,u1) :: Gamma) |- s2 <: t2 ==>
          Gamma |- ForallTy x u1 s2 <: ForallTy x u1 t2)
`;

val fsubtyping_swap = store_thm(
  "fsubtyping_swap",
  ``!Gamma ty1 ty2.
        Gamma |- ty1 <: ty2 ==>
        fsubtyping (ctxtswap x y Gamma) (fswap x y ty1) (fswap x y ty2)``,
  HO_MATCH_MP_TAC fsubtyping_ind THEN
  REPEAT CONJ_TAC THENL [
    (* refl *)  SRW_TAC [][SUBSET_DEF, fsubtyping_rules],
    (* trans *) METIS_TAC [fsubtyping_rules],
    (* top *)   SRW_TAC [][fsubtyping_rules, fswap_thm,
                           SUBSET_DEF],
    (* tvar *)  SRW_TAC [][fswap_thm, fsubtyping_rules],
    (* fun *)   SRW_TAC [][fsubtyping_rules, fswap_thm],
    (* forall *)SRW_TAC [][fsubtyping_rules, fswap_thm, SUBSET_DEF]
  ]);

val fsubtyping_fv_constraint = store_thm(
  "fsubtyping_fv_constraint",
  ``!G ty1 ty2. G |- ty1 <: ty2 ==>
                ftyFV ty1 SUBSET cdom G /\
                ftyFV ty2 SUBSET cdom G``,
  HO_MATCH_MP_TAC fsubtyping_ind THEN
  SRW_TAC [][SUBSET_DEF] THEN METIS_TAC [wfctxt_MEM]);

val fsubtyping_wfctxt = store_thm(
  "fsubtyping_wfctxt",
  ``!G ty1 ty2. G |- ty1 <: ty2 ==> wfctxt G``,
  HO_MATCH_MP_TAC fsubtyping_ind THEN SRW_TAC [][]);

val _ = remove_rules_for_term "dSUB"

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 425),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "|->", BreakSpace(1, 0),
                                 BeginFinalBlock(PP.INCONSISTENT, 2),
                                 TM, HardSpace 1, TOK "<:", BreakSpace(1,0)],
                  term_name = "alg_subtyping"}

val (algn_subtyping_rules, algn_subtyping_ind, algn_subtyping_cases) =
  Hol_reln`
    (!Gamma s. wfctxt Gamma /\ ftyFV s SUBSET cdom Gamma ==>
               algn_subtyping 0 Gamma s Top) /\
    (!Gamma x. wfctxt Gamma /\ x IN cdom Gamma ==>
               algn_subtyping 0 Gamma (TyVar x) (TyVar x)) /\
    (!Gamma x u t n. MEM (x, u) Gamma /\ algn_subtyping n Gamma u t ==>
                     algn_subtyping (n + 1) Gamma (TyVar x) t) /\
    (!Gamma t1 s1 t2 s2 n m.
                 algn_subtyping n Gamma t1 s1 /\
                 algn_subtyping m Gamma s2 t2 ==>
                 algn_subtyping (MAX n m + 1) Gamma (Fun s1 s2) (Fun t1 t2)) /\
    (!Gamma x u1 s2 t2 n.
                 ~(x IN ftyFV u1) /\ ~(x IN cdom Gamma) /\
                 ftyFV u1 SUBSET cdom Gamma /\
                 algn_subtyping n ((x,u1)::Gamma) s2 t2 ==>
                 algn_subtyping (n + 1) Gamma (ForallTy x u1 s2)
                                              (ForallTy x u1 t2))
`;

val algn_subtyping_fswap = store_thm(
  "algn_subtyping_fswap",
  ``!n G ty1 ty2. algn_subtyping n G ty1 ty2 ==>
                  !x y. algn_subtyping n (ctxtswap x y G)
                                         (fswap x y ty1)
                                         (fswap x y ty2)``,
  HO_MATCH_MP_TAC algn_subtyping_ind THEN REPEAT CONJ_TAC THEN
  SRW_TAC [][fswap_thm, algn_subtyping_rules] THEN
  METIS_TAC [algn_subtyping_rules, MEM_ctxtswap, fswap_inv,
             swapTheory.swapstr_inverse]);

val algn_subtyping_fswap1_eq = store_thm(
  "algn_subtyping_fswap1_eq",
  ``algn_subtyping n G (fswap x y ty1) ty2 =
    algn_subtyping n (ctxtswap x y G) ty1 (fswap x y ty2)``,
  METIS_TAC [algn_subtyping_fswap, fswap_inv, ctxtswap_inv]);

val algn_subtyping_wfctxt = store_thm(
  "algn_subtyping_wfctxt",
  ``!n G ty1 ty2. algn_subtyping n G ty1 ty2 ==> wfctxt G``,
  HO_MATCH_MP_TAC algn_subtyping_ind THEN SRW_TAC [][]);

val alg_subtyping_def = Define`
  Gamma |-> s <: t = ?n. algn_subtyping n Gamma s t
`;

val alg_subtyping_fswap1_eq = store_thm(
  "alg_subtyping_fswap1_eq",
  ``Gamma |-> fswap x y ty1 <: ty2 =
    ctxtswap x y Gamma |-> ty1 <: fswap x y ty2``,
  METIS_TAC [alg_subtyping_def, algn_subtyping_fswap1_eq]);

val alg_subtyping_rules = store_thm(
  "alg_subtyping_rules",
  ``(!G s. wfctxt G /\ ftyFV s SUBSET cdom G ==> G |-> s <: Top) /\
    (!G x. wfctxt G /\ x IN cdom G ==> G |-> TyVar x <: TyVar x) /\
    (!G x u t. MEM (x, u) G /\ G |-> u <: t ==> G |-> TyVar x <: t) /\
    (!G t1 s1 t2 s2. G |-> t1 <: s1 /\ G |-> s2 <: t2 ==>
                     G |-> Fun s1 s2 <: Fun t1 t2) /\
    (!G x u1 s2 t2.
       ~(x IN ftyFV u1) /\ ~(x IN cdom G) /\ ftyFV u1 SUBSET cdom G /\
       ((x,u1) :: G) |-> s2 <: t2 ==>
       G |-> ForallTy x u1 s2 <: ForallTy x u1 t2)``,
  SRW_TAC [][alg_subtyping_def] THEN METIS_TAC [algn_subtyping_rules]);

val alg_subtyping_ind =
    (Q.GEN `P` o
     SIMP_RULE (srw_ss()) [GSYM alg_subtyping_def] o
     CONV_RULE (RAND_CONV
                  (SWAP_VARS_CONV THENC
                   BINDER_CONV (SWAP_VARS_CONV THENC
                                BINDER_CONV (SWAP_VARS_CONV THENC
                                             BINDER_CONV FORALL_IMP_CONV)))) o
     SIMP_RULE (srw_ss()) [] o
     Q.SPEC `\n G ty1 ty2. P G ty1 ty2`) algn_subtyping_ind

val alg_subtyping_cases =
    (REWRITE_CONV [alg_subtyping_def] THENC
     ONCE_REWRITE_CONV [algn_subtyping_cases] THENC
     SIMP_CONV (srw_ss()) [EXISTS_OR_THM] THENC
     SIMP_CONV (srw_ss())
               (map (INST_TYPE [alpha |-> numSyntax.num])
                    [LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM]) THENC
     REWRITE_CONV [GSYM alg_subtyping_def])
      ``Gamma |-> ty1 <: ty2``

val strong_alg_subtyping_ind =
    IndDefRules.derive_strong_induction (CONJUNCTS alg_subtyping_rules,
                                         alg_subtyping_ind)

val alg_subtyping_refl (* lemma 28.3.1 *) = store_thm(
  "alg_subtyping_refl",
  ``!ty G. wfctxt G /\ ftyFV ty SUBSET cdom G ==> G |-> ty <: ty``,
  HO_MATCH_MP_TAC fsubty_ind THEN
  SRW_TAC [][alg_subtyping_rules] THEN
  Q_TAC (NEW_TAC "z") `cdom G UNION ftyFV ty UNION ftyFV ty'` THEN
  `ForallTy v ty ty' = ForallTy z ty (fswap z v ty')`
    by SRW_TAC [][ForallTy_ALPHA] THEN
  SRW_TAC [][] THEN
  MATCH_MP_TAC (last (CONJUNCTS alg_subtyping_rules)) THEN
  SRW_TAC [][alg_subtyping_fswap1_eq] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
  METIS_TAC [swapTheory.swapstr_def]);
val _ = export_rewrites ["alg_subtyping_refl"]

val alg_subtyping_top_left = store_thm(
  "alg_subtyping_top_left",
  ``!Gamma t. wfctxt Gamma ==> (Gamma |-> Top <: t = (t = Top))``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM, alg_subtyping_rules] THEN
  ONCE_REWRITE_TAC [alg_subtyping_cases] THEN
  SRW_TAC [][]);
val _ = export_rewrites ["alg_subtyping_top_left"]

val alg_subtyping_tyvar_right0 = prove(
  ``!Gamma ty1 ty2. Gamma |-> ty1 <: ty2 ==>
                    !x. (ty2 = TyVar x) ==>
                        ?y. ty1 = TyVar y``,
  HO_MATCH_MP_TAC alg_subtyping_ind THEN SRW_TAC [][]);
val alg_subtyping_tyvar_right = save_thm(
  "alg_subtyping_tyvar_right",
  SIMP_RULE (bool_ss ++ DNF_ss) [] alg_subtyping_tyvar_right0)

val algn_subtyping_ftyFVs_in_ctxt = store_thm(
  "algn_subtyping_ftyFVs_in_ctxt",
  ``!n G ty1 ty2. algn_subtyping n G ty1 ty2 ==>
                  ftyFV ty1 SUBSET cdom G /\ ftyFV ty2 SUBSET cdom G``,
  HO_MATCH_MP_TAC algn_subtyping_ind THEN
  SRW_TAC [][SUBSET_DEF] THEN METIS_TAC [cdom_MEM])

(* important to have this sort of inversion theorem, where you get the
   same bound variable in the "other" position of the relation.  By
   analogy, in the lambda calculus with beta reduction, you have to prove
   that if
     LAM v bod --> t
   then
     ?bod'. (t = LAM v bod') /\ bod --> bod'
   In the lambda calculus, it's always possible to get this v (which
   has to do with the fact that beta reduction doesn't produce extra
   free variables).  In F<:, your x has to satisfy certain constraints.
*)
val algn_subtyping_ForallTy_eqn = store_thm(
  "algn_subtyping_ForallTy_eqn",
  ``~(x IN ftyFV bnd) /\ ~(x IN cdom G) ==>
    (algn_subtyping p G (ForallTy x bnd ty) t =
       wfctxt G /\
       ((t = Top) /\ (p = 0) /\ ftyFV (ForallTy x bnd ty) SUBSET cdom G \/
        (?ty' p0. (t = ForallTy x bnd ty') /\ ftyFV bnd SUBSET cdom G /\
                  (p = p0 + 1) /\
                  algn_subtyping p0 ((x,bnd)::G) ty ty')))``,
  SIMP_TAC (srw_ss() ++ DNF_ss ++ SatisfySimps.SATISFY_ss)
           [EQ_IMP_THM, algn_subtyping_rules, algn_subtyping_wfctxt] THEN
  STRIP_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [algn_subtyping_cases])) THEN
  ASM_SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN
  Q_TAC SUFF_TAC
        `!y bnd2 ty2 ty3 n.
             (p = n + 1) /\ (ForallTy y bnd2 ty2 = ForallTy x bnd ty) /\
             (t = ForallTy y bnd2 ty3) /\ ~(y IN ftyFV bnd2) /\
             ~(y IN cdom G) /\ ftyFV bnd2 SUBSET cdom G /\
             algn_subtyping n ((y,bnd2)::G) ty2 ty3 ==>
             ?ty'.
                (ForallTy x bnd ty' = ForallTy y bnd2 ty3) /\
                ftyFV bnd SUBSET cdom G /\
                algn_subtyping n ((x,bnd)::G) ty ty'` THEN1 METIS_TAC [] THEN
  ASM_SIMP_TAC (srw_ss() ++ DNF_ss)
               [ForallTy_11, algn_subtyping_fswap1_eq] THEN
  SRW_TAC [][fswap_comm] THEN
  `wfctxt G` by (IMP_RES_TAC algn_subtyping_wfctxt THEN
                 FULL_SIMP_TAC (srw_ss()) []) THEN
  Q.PAT_ASSUM `algn_subtyping V X Y Z` MP_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [fswap_fresh, ctxtswap_fresh,
                           wfctxt_ctxtFV_cdom] THEN
  Cases_on `x = y` THEN SRW_TAC [][] THEN
  STRIP_TAC THEN
  `y IN ftyFV (fswap x y ty3)` by SRW_TAC [][] THEN
  `y IN cdom ((x,bnd)::G)` by METIS_TAC [SUBSET_DEF,
                                         algn_subtyping_ftyFVs_in_ctxt] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val algn_subtyping_trans = prove(
  ``!n m p Gamma s q t.
         (n = m + p) /\
         algn_subtyping m Gamma s q /\
         algn_subtyping p Gamma q t ==>
         ?r. algn_subtyping r Gamma s t``,
  HO_MATCH_MP_TAC arithmeticTheory.COMPLETE_INDUCTION THEN
  REPEAT STRIP_TAC THEN
  Q.PAT_ASSUM `algn_subtyping m Gamma s q`
              (MP_TAC o ONCE_REWRITE_RULE [algn_subtyping_cases]) THEN
  SRW_TAC [][] THENL [
    METIS_TAC [alg_subtyping_def, alg_subtyping_top_left,
               algn_subtyping_rules],
    METIS_TAC [],
    FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN
    `?r. algn_subtyping r Gamma u t`
       by METIS_TAC [DECIDE ``n + p < n + 1 + p``] THEN
    METIS_TAC [algn_subtyping_rules],
    Q.PAT_ASSUM `algn_subtyping p Gamma (Fun t1 t2) t`
                (MP_TAC o ONCE_REWRITE_RULE [algn_subtyping_cases]) THEN
    SRW_TAC [][] THEN1 METIS_TAC [algn_subtyping_rules,
                                  algn_subtyping_ftyFVs_in_ctxt] THEN
    FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [AND_IMP_INTRO] THEN
    `?r. algn_subtyping r Gamma t1' s1`
        by (FIRST_X_ASSUM MATCH_MP_TAC THEN
            MAP_EVERY Q.EXISTS_TAC [`n'`, `n`, `t1`] THEN
            ASM_SIMP_TAC arith_ss [arithmeticTheory.MAX_DEF]) THEN
    `?r'. algn_subtyping r' Gamma s2 t2'`
        by (FIRST_X_ASSUM MATCH_MP_TAC THEN
            MAP_EVERY Q.EXISTS_TAC [`m'`, `m`, `t2`] THEN
            ASM_SIMP_TAC arith_ss [arithmeticTheory.MAX_DEF]) THEN
    METIS_TAC [algn_subtyping_rules],
    Q.PAT_ASSUM `algn_subtyping p Gamma (ForallTy x u1 t2) t` MP_TAC THEN
    ASM_SIMP_TAC (srw_ss()) [algn_subtyping_ForallTy_eqn] THEN
    SRW_TAC [][] THENL [
      (* case where it's less than Top *)
      IMP_RES_TAC algn_subtyping_ftyFVs_in_ctxt THEN
      FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN METIS_TAC [],
      ALL_TAC
    ] THEN
    SRW_TAC [][ForallTy_11] THEN
    METIS_TAC [DECIDE ``n + p0 < n + 1 + (p0 + 1)``]
  ]);

val alg_subtyping_trans (* lemma 28.3.2 *) = store_thm(
  "alg_subtyping_trans",
  ``!Gamma s q. Gamma |-> s <: q /\ Gamma |-> q <: t ==>
                Gamma |-> s <: t``,
  METIS_TAC [alg_subtyping_def, algn_subtyping_trans]);

val alg_soundcomplete (* theorem 28.3.3 *) = store_thm(
  "alg_soundcomplete",
  ``G |- ty1 <: ty2 = G |-> ty1 <: ty2``,
  EQ_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`ty2`, `ty1`, `G`] THENL [
    HO_MATCH_MP_TAC fsubtyping_ind THEN SRW_TAC [][alg_subtyping_rules] THENL [
      METIS_TAC [alg_subtyping_trans],
      `Gamma |-> ty <: ty`
         by METIS_TAC [alg_subtyping_refl, wfctxt_MEM, SUBSET_DEF] THEN
      METIS_TAC [alg_subtyping_rules]
    ],
    HO_MATCH_MP_TAC alg_subtyping_ind THEN SRW_TAC [][fsubtyping_rules] THEN
    METIS_TAC [fsubtyping_rules, wfctxt_MEM, SUBSET_DEF,
               fsubtyping_wfctxt]
  ]);

val _ = export_theory ();
