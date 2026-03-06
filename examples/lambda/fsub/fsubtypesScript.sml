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

   This theory establishes the type, along with swap functions for the type
   and the type of "contexts", which are of type (string * type) list

*)
Theory fsubtypes
Libs
  binderLib metisLib BasicProvers boolSimps


val SUBSET_DEF = pred_setTheory.SUBSET_DEF

(* establish the inductive characterisation of the encoding above *)
val (fsubrep_rules, fsubrep_ind, fsubrep_cases) = Hol_reln`
  fsubrep (CON T) /\
  (!v t t'. fsubrep t /\ fsubrep t' ==> fsubrep (CON F @@ t @@ LAM v t')) /\
  (!s. fsubrep (VAR s)) /\
  (!t u. fsubrep t /\ fsubrep u ==> fsubrep (t @@ u))
`;

val strong_fsubrep_ind = save_thm(
  "strong_fsubrep_ind",
  IndDefLib.derive_strong_induction (fsubrep_rules, fsubrep_ind));

(* because this is not obviously non-overlapping, we need to prove that
   certain patterns aren't in fsubrep by induction *)

val lam_not_fsubrep0 = prove(
  ``!t0. fsubrep t0 ==> !v t. (t0 = LAM v t) ==> F``,
  HO_MATCH_MP_TAC fsubrep_ind THEN SRW_TAC [][]);
val lam_not_fsubrep = save_thm(
  "lam_not_fsubrep",
  SIMP_RULE (srw_ss() ++ DNF_ss) [] lam_not_fsubrep0)
val _ = export_rewrites ["lam_not_fsubrep"]

Theorem CONF_not_fsubrep:
    ~(fsubrep (CON F))
Proof
  ONCE_REWRITE_TAC [fsubrep_cases] THEN SRW_TAC [][]
QED
val _ = export_rewrites ["CONF_not_fsubrep"]

(* type can be established by showing that fsubrep is non-empty; CON T is
   the witness *)
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
Theorem fsubty2term_11:
    (fsubty2term ty1 = fsubty2term ty2) = (ty1 = ty2)
Proof
  SRW_TAC [][EQ_IMP_THM] THEN
  METIS_TAC [bijections_exist]
QED
val _ = export_rewrites ["fsubty2term_11"]

Theorem term2fsubty_11:
    fsubrep t1 /\ fsubrep t2 ==>
    ((term2fsubty t1 = term2fsubty t2) = (t1 = t2))
Proof
  SRW_TAC [][EQ_IMP_THM] THEN METIS_TAC [bijections_exist]
QED

Theorem fsubrep_fsubty2term:
    fsubrep (fsubty2term ty1)
Proof
  METIS_TAC [bijections_exist]
QED
val _ = export_rewrites ["fsubrep_fsubty2term"]


(* define constructors *)
Definition Top_def:  Top = term2fsubty (CON T)
End
Definition TyVar_def:  TyVar s = term2fsubty (VAR s)
End
Definition Fun_def:
  Fun ty1 ty2 = term2fsubty (fsubty2term ty1 @@ fsubty2term ty2)
End
Definition ForallTy_def:
  ForallTy v boundty ty =
    term2fsubty (CON F @@ fsubty2term boundty @@ LAM v (fsubty2term ty))
End

(* prove injectivity for the non-binder constructors *)
Theorem Fun_11:
    (Fun ty1 ty2 = Fun ty3 ty4) = (ty1 = ty3) /\ (ty2 = ty4)
Proof
  SIMP_TAC (srw_ss()) [Fun_def, EQ_IMP_THM, fsubrep_rules, term2fsubty_11]
QED
val _ = export_rewrites ["Fun_11"]

Theorem TyVar_11:
    (TyVar s1 = TyVar s2) = (s1 = s2)
Proof
  SIMP_TAC (srw_ss()) [TyVar_def, fsubrep_rules, term2fsubty_11]
QED
val _ = export_rewrites ["TyVar_11"]

(* prove distinctness *)
Theorem fsubty_distinct:
    ~(Top = TyVar s) /\ ~(Top = Fun ty1 ty2) /\ ~(Top = ForallTy v bnd ty) /\
    ~(TyVar s = Fun ty1 ty2) /\ ~(TyVar s = ForallTy v bnd ty) /\
    ~(Fun ty1 ty2 = ForallTy v bnd ty)
Proof
  SRW_TAC [][Top_def, TyVar_def, Fun_def, ForallTy_def,
             fsubrep_rules, term2fsubty_11] THEN
  DISJ2_TAC THEN STRIP_TAC THEN
  POP_ASSUM (MP_TAC o Q.AP_TERM `fsubrep`) THEN
  SRW_TAC [][]
QED
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
Theorem fsubty_ind:
    !P.
        P Top /\
        (!ty1 ty2. P ty1 /\ P ty2 ==> P (Fun ty1 ty2)) /\
        (!s. P (TyVar s)) /\
        (!v bnd ty. P bnd /\ P ty ==> P (ForallTy v bnd ty)) ==>
        !ty. P ty
Proof
  SIMP_TAC (srw_ss())
           [forall_fsubty, Top_def, TyVar_def, Fun_def, ForallTy_def,
            rep_abs_lemma] THEN
  GEN_TAC THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC strong_fsubrep_ind THEN
  METIS_TAC []
QED

(* definition of swap *)
Definition fswap_def:
  fswap x y ty = term2fsubty (swap x y (fsubty2term ty))
End

Theorem fsubrep_swap:
    !t. fsubrep t ==> !x y. fsubrep (swap x y t)
Proof
  HO_MATCH_MP_TAC fsubrep_ind THEN
  SRW_TAC [][swapTheory.swap_thm, fsubrep_rules]
QED

Theorem fswap_thm:
    (!s. fswap x y (TyVar s) = TyVar (swapstr x y s)) /\
    (!ty1 ty2. fswap x y (Fun ty1 ty2) =
                 Fun (fswap x y ty1) (fswap x y ty2)) /\
    (fswap x y Top = Top) /\
    (!v bnd ty. fswap x y (ForallTy v bnd ty) =
       ForallTy (swapstr x y v) (fswap x y bnd) (fswap x y ty))
Proof
  SRW_TAC [][fswap_def, Top_def, ForallTy_def, Fun_def, TyVar_def,
             rep_abs_lemma, fsubrep_rules, swapTheory.swap_thm,
             fsubrep_swap]
QED
val _ = export_rewrites ["fswap_thm"]

Theorem fswap_inv:
    !ty x y. fswap x y (fswap x y ty) = ty
Proof
  HO_MATCH_MP_TAC fsubty_ind THEN SRW_TAC [][]
QED
val _ = export_rewrites ["fswap_inv"]

Theorem fswap_id:
    fswap x x ty = ty
Proof
  SRW_TAC [][fswap_def, bijections_exist]
QED
val _ = export_rewrites ["fswap_id"]

Theorem fswap_comm:
    fswap y x = fswap x y
Proof
  SRW_TAC [][FUN_EQ_THM, fswap_def, swapTheory.swap_comm]
QED
val _ = export_rewrites ["fswap_comm"]

(* define swap over contexts *)
Definition ctxtswap_def:
  (ctxtswap x y [] = []) /\
  (ctxtswap x y (h::t) = (swapstr x y (FST h), fswap x y (SND h)) ::
                         ctxtswap x y t)
End
val _ = export_rewrites ["ctxtswap_def"]

Theorem ctxtswap_inv:
    !G x y. ctxtswap x y (ctxtswap x y G) = G
Proof
  Induct THEN SRW_TAC [][]
QED
val _ = export_rewrites ["ctxtswap_inv"]

Theorem ctxtswap_id:
    !G x y. ctxtswap x x G = G
Proof
  Induct THEN SRW_TAC [][ctxtswap_def]
QED
val _ = export_rewrites ["ctxtswap_id"]

Theorem MEM_ctxtswap:
    !G x y v ty. MEM (v,ty) (ctxtswap x y G) =
                 MEM (swapstr x y v, fswap x y ty) G
Proof
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  METIS_TAC [fswap_inv]
QED
val _ = export_rewrites ["MEM_ctxtswap"]

Definition cdom_def:
  (cdom ([]: (string # fsubty) list)  = {}) /\
  (cdom (h::t) = FST h INSERT cdom t)
End
val _ = export_rewrites ["cdom_def"]

Theorem FINITE_cdom:
    !G. FINITE (cdom G)
Proof
  Induct THEN SRW_TAC [][]
QED
val _ = export_rewrites ["FINITE_cdom"]

Theorem cdom_MEM:
    x IN cdom G = ?ty. MEM (x,ty) G
Proof
  Induct_on `G` THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  METIS_TAC []
QED

(* define fv for types *)
Definition ftyFV_def:
  ftyFV ty = FV (fsubty2term ty)
End

Theorem ftyFV_thm:
    (ftyFV Top = {}) /\
    (ftyFV (Fun ty1 ty2) = ftyFV ty1 UNION ftyFV ty2) /\
    (ftyFV (TyVar s) = {s}) /\
    (ftyFV (ForallTy v bnd ty) = ftyFV bnd UNION (ftyFV ty DELETE v))
Proof
  SRW_TAC [][ftyFV_def, Top_def, Fun_def, ForallTy_def, TyVar_def,
             rep_abs_lemma, fsubrep_rules]
QED
val _ = export_rewrites ["ftyFV_thm"]

(* the following is not really an injectivity result, but it seems the best
   possible for ForallTy *)
Theorem ForallTy_11:
    (ForallTy v1 bnd1 bod1 = ForallTy v2 bnd2 bod2) =
      (bnd1 = bnd2) /\ ((v1 = v2) \/ ~(v1 IN ftyFV bod2)) /\
      (bod1 = fswap v1 v2 bod2)
Proof
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
  ]
QED

Theorem ForallTy_injectivity_lemma1:
    (ForallTy x bnd1 ty1 = ForallTy y bnd2 ty2) ==>
    (bnd1 = bnd2) /\ (ty2 = fswap x y ty1)
Proof
  METIS_TAC [ForallTy_11, fswap_inv]
QED

Theorem ForallTy_INJ_ALPHA_FV:
    (ForallTy x bnd ty1 = ForallTy y bnd ty2) /\ ~(x = y) ==>
    ~(x IN ftyFV ty2) /\ ~(y IN ftyFV ty1)
Proof
  METIS_TAC [ForallTy_11]
QED

Theorem ForallTy_ALPHA:
    ~(u IN ftyFV ty) ==>
    (ForallTy u bnd (fswap u v ty) = ForallTy v bnd ty)
Proof
  METIS_TAC [ForallTy_11]
QED

Theorem fswap_fresh:
    !ty x y. ~(x IN ftyFV ty) /\ ~(y IN ftyFV ty) ==>
             (fswap x y ty = ty)
Proof
  SRW_TAC [][fswap_def, ftyFV_def, swapTheory.swap_identity,
             bijections_exist]
QED

Theorem swapset_DELETE:
    swapset x y (s1 DELETE s) = swapset x y s1 DELETE swapstr x y s
Proof
  SRW_TAC [][swapTheory.swapset_def, pred_setTheory.EXTENSION]
QED

Theorem swapset_SUBSET:
    s1 SUBSET swapset x y s2 = swapset x y s1 SUBSET s2
Proof
  SRW_TAC [][swapTheory.swapset_def, SUBSET_DEF] THEN
  METIS_TAC [swapTheory.swapstr_inverse]
QED
val _ = export_rewrites ["swapset_SUBSET"]

Theorem ftyFV_fswap:
    !ty x y. ftyFV (fswap x y ty) = swapset x y (ftyFV ty)
Proof
  HO_MATCH_MP_TAC fsubty_ind THEN
  SRW_TAC [][swapTheory.swapset_UNION, swapset_DELETE]
QED
val _ = export_rewrites ["ftyFV_fswap"]

Theorem ftyFV_FINITE:
    !ty. FINITE (ftyFV ty)
Proof
  HO_MATCH_MP_TAC fsubty_ind THEN
  SRW_TAC [][]
QED
val _ = export_rewrites ["ftyFV_FINITE"]

(* define FV for ctxts *)
Definition ctxtFV_def:
  (ctxtFV [] = {}) /\
  (ctxtFV (h::t) = {FST h} UNION ftyFV (SND h) UNION ctxtFV t)
End
val _ = export_rewrites ["ctxtFV_def"]

Theorem ctxtFV_ctxtswap:
    !G x y. ctxtFV (ctxtswap x y G) = swapset x y (ctxtFV G)
Proof
  Induct THEN SRW_TAC [][swapTheory.swapset_UNION]
QED
val _ = export_rewrites ["ctxtFV_ctxtswap"]

Theorem ctxtFV_FINITE:
    !G. FINITE (ctxtFV G)
Proof
  Induct THEN SRW_TAC [][]
QED
val _ = export_rewrites ["ctxtFV_FINITE"]

Theorem cdom_SUBSET_ctxtFV:
    !G. cdom G SUBSET ctxtFV G
Proof
  Induct THEN
  FULL_SIMP_TAC (srw_ss()) [cdom_def, SUBSET_DEF] THEN
  METIS_TAC []
QED

Theorem cdom_ctxtswap:
    !G x y. cdom (ctxtswap x y G) = swapset x y (cdom G)
Proof
  Induct THEN SRW_TAC[][]
QED
val _ = export_rewrites ["cdom_ctxtswap"]

Theorem ctxtswap_fresh:
    !G x y.
       ~(x IN ctxtFV G) /\ ~(y IN ctxtFV G) ==>
       (ctxtswap x y G = G)
Proof
  Induct THEN SRW_TAC [][fswap_fresh]
QED

(* wfctxt implements the restrictions defined on pp393-4 *)
Definition wfctxt_def:
  (wfctxt [] = T) /\
  (wfctxt ((x,ty) :: t) = ~(x IN cdom t) /\
                          ftyFV ty SUBSET cdom t /\
                          wfctxt t)
End
val _ = export_rewrites ["wfctxt_def"]

Theorem wfctxt_swap:
    !G x y. wfctxt (ctxtswap x y G) = wfctxt G
Proof
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]
QED
val _ = export_rewrites ["wfctxt_swap"]

Theorem wfctxt_ctxtFV_cdom:
    !G. wfctxt G ==> (ctxtFV G = cdom G)
Proof
  SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION] THEN
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, SUBSET_DEF] THEN
  METIS_TAC []
QED

Theorem wfctxt_MEM:
    !G. wfctxt G /\ MEM (x,ty) G ==>
        x IN cdom G /\ !y. y IN ftyFV ty ==> y IN cdom G
Proof
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD,
                                       SUBSET_DEF] THEN
  METIS_TAC []
QED

Definition fsize_def:
  fsize (t:fsubty) = size (fsubty2term t)
End

Theorem fsize_thm:
    (fsize Top = 1) /\
    (fsize (TyVar s) = 1) /\
    (fsize (ForallTy x ty1 ty2) = fsize ty1 + fsize ty2 + 4) /\
    (fsize (Fun ty1 ty2) = fsize ty1 + fsize ty2 + 1)
Proof
  SRW_TAC [numSimps.ARITH_ss]
          [fsize_def,Fun_def,Top_def,ForallTy_def,TyVar_def,
           rep_abs_lemma, fsubrep_rules, ncTheory.size_thm]
QED


