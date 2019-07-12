(* Fun and games with the "locally nameless" approach to language meta-theory
   as done in the POPL paper "Engineering Formal Metatheory" by Brian
   Aydemir, Arthur Charguéraud, Benjamin Pierce, Randy Pollack and Stephanie
   Weirich.

   Contribution below is to show that it's as easy to prove the
   cofinite introduction rule and the cofinite induction principle of
   the original relations directly, rather than bothering to define a
   whole new cofinite relation and to then show that this is
   equivalent to the original.
*)

open HolKernel boolLib bossLib Parse

open binderLib

open nomsetTheory pred_setTheory

fun Store_thm (p as (n,t,tac)) = store_thm p before export_rewrites [n]

val _ = new_theory "lnameless"

val _ = Datatype`lnt = var string | bnd num | app lnt lnt | abs lnt`;

val open_def = Define`
  (open k u (bnd i) = if i = k then u else bnd i) /\
  (open k u (var s) = var s) /\
  (open k u (app t1 t2) = app (open k u t1) (open k u t2)) /\
  (open k u (abs t) = abs (open (k + 1) u t))
`;
val _ = export_rewrites ["open_def"]

val raw_lnpm_def = Define`
  (raw_lnpm pi (var s) = var (lswapstr pi s)) /\
  (raw_lnpm pi (bnd i) = bnd i) /\
  (raw_lnpm pi (app t1 t2) = app (raw_lnpm pi t1) (raw_lnpm pi t2)) /\
  (raw_lnpm pi (abs t) = abs (raw_lnpm pi t))
`;
val _ = export_rewrites ["raw_lnpm_def"]

val _ = overload_on("ln_pmact",``mk_pmact raw_lnpm``);
val _ = overload_on("lnpm",``pmact ln_pmact``);

val lnpm_raw = store_thm(
  "lnpm_raw",
  ``lnpm = raw_lnpm``,
  SRW_TAC [][GSYM pmact_bijections] THEN
  SRW_TAC [][is_pmact_def, permeq_thm, FUN_EQ_THM] THENL [
    Induct_on `x` THEN SRW_TAC [][],
    Induct_on `x` THEN SRW_TAC [][pmact_decompose],
    Induct_on `x` THEN SRW_TAC [][]
  ]);

val lnpm_thm = save_thm(
"lnpm_thm",
raw_lnpm_def |> SUBS [GSYM lnpm_raw]);
val _ = export_rewrites["lnpm_thm"];

val lnpm_open = prove(
  ``!i. lnpm pi (open i t1 t2) = open i (lnpm pi t1) (lnpm pi t2)``,
  Induct_on `t2` THEN SRW_TAC [][]);

val fv_def = Define`
  (fv (var s) = {s}) /\
  (fv (bnd i) = {}) /\
  (fv (app t u) = fv t UNION fv u) /\
  (fv (abs t) = fv t)
`;
val _ = export_rewrites ["fv_def"]

val fv_lnpm = prove(
  ``!t. fv (lnpm pi t) = ssetpm pi (fv t)``,
  Induct THEN SRW_TAC [][pmact_INSERT, pmact_UNION]);

val FINITE_fv = Store_thm(
  "FINITE_fv",
  ``!t. FINITE (fv t)``,
  Induct THEN SRW_TAC [][]);

val lnpm_fresh = store_thm(
  "lnpm_fresh",
  ``~(a IN fv t) /\ ~(b IN fv t) ==> (lnpm [(a,b)] t = t)``,
  Induct_on `t` THEN SRW_TAC [][]);

val (lclosed_rules, lclosed_ind, lclosed_cases) = Hol_reln`
  (!s. lclosed (var s)) /\
  (!t1 t2. lclosed t1 /\ lclosed t2 ==> lclosed (app t1 t2)) /\
  (!s t. ~(s IN fv t) /\ lclosed (open 0 (var s) t) ==>
         lclosed (abs t))
`;

val lclosed_eqvt = prove(
  ``!t. lclosed t ==> !pi. lclosed (lnpm pi t)``,
  HO_MATCH_MP_TAC lclosed_ind THEN SRW_TAC [][lclosed_rules, lnpm_open] THEN
  MATCH_MP_TAC (last (CONJUNCTS lclosed_rules)) THEN
  Q.EXISTS_TAC `lswapstr pi s` THEN
  SRW_TAC [][fv_lnpm]);

val lclosed_gen_bvc_ind = store_thm(
  "lclosed_gen_bvc_ind",
  ``!P f. (!c. FINITE (f c)) /\
           (!s c. P (var s) c) /\
           (!t1 t2 c. (!d. P t1 d) /\ (!d. P t2 d) ==> P (app t1 t2) c) /\
           (!s t c. ~(s IN f c) /\ ~(s IN fv t) /\
                    (!d. P (open 0 (var s) t) d) ==>
                    P (abs t) c) ==>
           !t. lclosed t ==> !c. P t c``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!t. lclosed t ==> !pi c. P (lnpm pi t) c`
        THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC lclosed_ind THEN SRW_TAC [][lnpm_open] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  Q_TAC (NEW_TAC "z") `fv (lnpm pi t) UNION f c` THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `(stringpm pi s, z) :: pi` MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  `lnpm [(stringpm pi s, z)] (lnpm pi t) = lnpm pi t`
     by SRW_TAC [][lnpm_fresh, fv_lnpm] THEN
  FULL_SIMP_TAC (srw_ss()) [GSYM pmact_decompose] THEN
  STRIP_TAC THEN Q.EXISTS_TAC `z` THEN SRW_TAC [][]);

val all_fnone = prove(
  ``(!(f:one -> 'a). P f) = !x:'a. P (K x)``,
  SRW_TAC [][EQ_IMP_THM] THEN
  Q_TAC SUFF_TAC `f = K (f())`
        THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][]) THEN
  SRW_TAC [][FUN_EQ_THM, oneTheory.one]);

val lclosed_bvc_ind = save_thm(
  "lclosed_bvc_ind",
  (Q.GEN `P` o Q.GEN `X` o
   SIMP_RULE bool_ss [] o
   SPECL [``(\M:lnt x:one. P M:bool)``,
          ``X:string -> bool``] o
   SIMP_RULE (srw_ss()) [all_fnone, oneTheory.one] o
   INST_TYPE [alpha |-> ``:one``] o
   GEN_ALL) lclosed_gen_bvc_ind);

val lclosed_cofin_ind = store_thm(
  "lclosed_cofin_ind",
  ``!P. (!s. P (var s)) /\
        (!t1 t2. P t1 /\ P t2 ==> P (app t1 t2)) /\
        (!t X. FINITE X /\
               (!s. ~(s IN X) ==> P (open 0 (var s) t)) ==>
               P (abs t)) ==>
        !t. lclosed t ==> P t``,
  GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!t. lclosed t ==> !pi. P (lnpm pi t)`
        THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC lclosed_bvc_ind THEN SRW_TAC [][lnpm_open] THEN
  Q.EXISTS_TAC `{}` THEN SRW_TAC [][] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  Q.EXISTS_TAC `fv (lnpm pi t)` THEN SRW_TAC [][] THEN
  `lnpm [(s',stringpm pi s)] (lnpm pi t) = lnpm pi t`
      by SRW_TAC [][lnpm_fresh, fv_lnpm] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `[(s',stringpm pi s)] ++ pi` MP_TAC) THEN
  SRW_TAC [][pmact_decompose]);

val abs_lclosed_I = store_thm(
  "abs_lclosed_I",
  ``FINITE X /\ (!s. ~(s IN X) ==> lclosed (open 0 (var s) t)) ==>
    lclosed (abs t)``,
  STRIP_TAC THEN MATCH_MP_TAC (last (CONJUNCTS lclosed_rules)) THEN
  Q_TAC (NEW_TAC "z") `fv t UNION X` THEN Q.EXISTS_TAC `z` THEN
  SRW_TAC [][]);

val strong_lclosed_cofin_ind = store_thm(
  "strong_lclosed_cofin_ind",
  ``!P. (!s. P (var s)) /\
        (!t1 t2. P t1 /\ P t2 /\ lclosed t1 /\ lclosed t2 ==>
                 P (app t1 t2)) /\
        (!t X. FINITE X /\
               (!s. ~(s IN X) ==> P (open 0 (var s) t) /\
                                  lclosed (open 0 (var s) t)) ==>
               P (abs t))
      ==>
        !t. lclosed t ==> P t``,
  GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!t. lclosed t ==> P t /\ lclosed t` THEN1 SRW_TAC [][] THEN
  HO_MATCH_MP_TAC lclosed_cofin_ind THEN
  METIS_TAC [abs_lclosed_I, lclosed_rules]);

val lclosed_E = store_thm(
  "lclosed_E",
  ``!t.
      lclosed t ==>
        (?s. (t = var s)) \/
        (?t1 t2. (t = app t1 t2) /\ lclosed t1 /\ lclosed t2) \/
        (?X u. (t = abs u) /\ FINITE X /\
               !s. ~(s IN X) ==> lclosed (open 0 (var s) u))``,
  HO_MATCH_MP_TAC strong_lclosed_cofin_ind THEN
  SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THEN
  METIS_TAC [lclosed_rules, abs_lclosed_I]);

val lclosed_abs_cofin = store_thm(
  "lclosed_abs_cofin",
  ``lclosed (abs t) = ?X. FINITE X /\
                          !s. ~(s IN X) ==> lclosed (open 0 (var s) t)``,
  EQ_TAC THEN STRIP_TAC THENL [
    IMP_RES_TAC lclosed_E THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [],
    METIS_TAC [abs_lclosed_I]
  ]);

val _ = Datatype `ltype = tyOne | tyFun ltype ltype`;

val _ = set_fixity "-->" (Infixr 700)
val _ = overload_on ("-->", ``tyFun``);

val valid_ctxt_def = Define`
  (valid_ctxt [] ⇔ T) /\
  (valid_ctxt ((x,A) :: G) ⇔ (!A'. ~MEM (x, A') G) /\ valid_ctxt G)
`;
val _ = export_rewrites ["valid_ctxt_def"]

(* permutation over contexts swaps the strings and leaves the types alone *)
val ctxtswap_def = Define`
  (ctxtswap pi [] = []) /\
  (ctxtswap pi (sA :: G) = (lswapstr pi (FST sA), SND sA) :: ctxtswap pi G)
`;
val _ = export_rewrites ["ctxtswap_def"]

val ctxtswap_NIL = store_thm(
  "ctxtswap_NIL",
  ``ctxtswap [] G = G``,
  Induct_on `G` THEN SRW_TAC [][]);
val _ = export_rewrites ["ctxtswap_NIL"]

val ctxtswap_inverse = store_thm(
  "ctxtswap_inverse",
  ``(ctxtswap pi (ctxtswap (REVERSE pi) G) = G) /\
    (ctxtswap (REVERSE pi) (ctxtswap pi G) = G)``,
  Induct_on `G` THEN SRW_TAC [][]);
val _ = export_rewrites ["ctxtswap_inverse"]

val ctxtswap_sing_inv = store_thm(
  "ctxtswap_sing_inv",
  ``ctxtswap [(x,y)] (ctxtswap [(x,y)] G) = G``,
  METIS_TAC [listTheory.APPEND, listTheory.REVERSE_DEF, ctxtswap_inverse]);
val _ = export_rewrites ["ctxtswap_sing_inv"]

val ctxtswap_APPEND = store_thm(
  "ctxtswap_APPEND",
  ``!p1 p2. ctxtswap (p1 ++ p2) G = ctxtswap p1 (ctxtswap p2 G)``,
  Induct_on `G` THEN SRW_TAC [][pmact_decompose]);

(* context membership "respects" permutation *)
val MEM_ctxtswap = store_thm(
  "MEM_ctxtswap",
  ``!G pi x A. MEM (lswapstr pi x, A) (ctxtswap pi G) = MEM (x,A) G``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);
val _ = export_rewrites ["MEM_ctxtswap"]

(* valid_ctxt also respects permutation *)
val valid_ctxt_swap0 = prove(
  ``!G. valid_ctxt G ==> !x y. valid_ctxt (ctxtswap pi G)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);
val valid_ctxt_swap = store_thm(
  "valid_ctxt_swap",
  ``valid_ctxt (ctxtswap pi G) = valid_ctxt G``,
  METIS_TAC [valid_ctxt_swap0, ctxtswap_inverse]);
val _ = export_rewrites ["valid_ctxt_swap"]

(* the free variables of a context, defined with primitive recursion to
   give us nice rewrites *)
val ctxtFV_def = Define`
  (ctxtFV [] = {}) /\
  (ctxtFV (h::t) = FST h INSERT ctxtFV t)
`;
val _ = export_rewrites ["ctxtFV_def"]

(* contexts have finitely many free variables *)
val FINITE_ctxtFV = store_thm(
  "FINITE_ctxtFV",
  ``FINITE (ctxtFV G)``,
  Induct_on `G` THEN SRW_TAC [][]);
val _ = export_rewrites ["FINITE_ctxtFV"]

val ctxtswap_fresh = store_thm(
  "ctxtswap_fresh",
  ``~(x IN ctxtFV G) /\ ~(y IN ctxtFV G) ==> (ctxtswap [(x,y)] G = G)``,
  Induct_on `G` THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);

val ctxtFV_ctxtswap = store_thm(
  "ctxtFV_ctxtswap",
  ``ctxtFV (ctxtswap pi G) = ssetpm pi (ctxtFV G)``,
  Induct_on `G` THEN SRW_TAC [][pmact_INSERT, stringpm_raw]);
val _ = export_rewrites ["ctxtFV_ctxtswap"]

(* more direct characterisation of ctxtFV *)
val ctxtFV_MEM = store_thm(
  "ctxtFV_MEM",
  ``x ∈ ctxtFV G ⇔ (∃A. MEM (x,A) G)``,
  Induct_on `G` THEN
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [pairTheory.FORALL_PROD]);


val valid_ctxt_CONS = prove(
  “!z ty. valid_ctxt ((z,ty) :: G) ⇔ z ∉ ctxtFV G ∧ valid_ctxt G”,
  Induct_on `G` THEN1 SRW_TAC [][] THEN
  ASM_SIMP_TAC bool_ss [pairTheory.FORALL_PROD, Once valid_ctxt_def] THEN
  SRW_TAC [][ctxtFV_MEM]);


val (typing_rules, typing_ind, typing_cases) = Hol_reln`
  (!G s ty. valid_ctxt G /\ MEM (s,ty) G ==> typing G (var s) ty) /\
  (!G t1 t2 ty1 ty2.
           typing G t1 (ty1 --> ty2) /\ typing G t2 ty1 ==>
           typing G (app t1 t2) ty2) /\
  (!G t s ty1 ty2.
           typing ((s,ty1)::G) (open 0 (var s) t) ty2 /\
           ~(s IN fv t)
         ==>
           typing G (abs t) (ty1 --> ty2))
`;

val typing_eqvt = store_thm(
  "typing_eqvt",
  ``!G t ty. typing G t ty ==> !pi. typing (ctxtswap pi G) (lnpm pi t) ty``,
  HO_MATCH_MP_TAC typing_ind THEN SRW_TAC [][typing_rules, lnpm_open] THENL [
    METIS_TAC [typing_rules],
    MATCH_MP_TAC (last (CONJUNCTS typing_rules)) THEN
    Q.EXISTS_TAC `lswapstr pi s` THEN
    SRW_TAC [][fv_lnpm]
  ]);


val typing_valid_ctxt = store_thm(
  "typing_valid_ctxt",
  ``!G t ty. typing G t ty ==> valid_ctxt G``,
  HO_MATCH_MP_TAC typing_ind THEN SRW_TAC [][]);

val typing_lclosed = store_thm(
  "typing_lclosed",
  ``!G t ty. typing G t ty ==> lclosed t``,
  HO_MATCH_MP_TAC typing_ind THEN SRW_TAC [][lclosed_rules] THEN
  METIS_TAC [lclosed_rules]);

val typing_bvc_ind = store_thm(
  "typing_bvc_ind",
  ``!P X. FINITE X /\
          (!G s ty. valid_ctxt G /\ MEM (s,ty) G ==> P G (var s) ty) /\
          (!G t1 t2 ty1 ty2.
               P G t1 (ty1 --> ty2) /\ P G t2 ty1 /\
               typing G t1 (ty1 --> ty2) /\ typing G t2 ty1 ==>
               P G (app t1 t2) ty2) /\
          (!G s t ty1 ty2.
               ~(s IN X) /\ ~(s IN fv t) /\
               P ((s,ty1)::G) (open 0 (var s) t) ty2 /\
               typing ((s,ty1)::G) (open 0 (var s) t) ty2
             ==>
               P G (abs t) (ty1 --> ty2))
        ==>
          !G t ty. typing G t ty ==> P G t ty``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!G t ty. typing G t ty ==>
                           !pi. typing (ctxtswap pi G) (lnpm pi t) ty /\
                                P (ctxtswap pi G) (lnpm pi t) ty`
        THEN1 METIS_TAC [pmact_nil, ctxtswap_NIL] THEN
  HO_MATCH_MP_TAC typing_ind THEN SRW_TAC [][lnpm_open, typing_rules] THENL [
    METIS_TAC [typing_rules],
    METIS_TAC [],
    MATCH_MP_TAC (last (CONJUNCTS typing_rules)) THEN
    Q.EXISTS_TAC `lswapstr pi s` THEN SRW_TAC [][fv_lnpm],

    Q_TAC (NEW_TAC "z") `fv (lnpm pi t) UNION X UNION
                         ctxtFV (ctxtswap pi G) UNION
                         {lswapstr pi s}` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN Q.EXISTS_TAC `z` THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `(lswapstr pi s, z) :: pi` MP_TAC) THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN
    STRIP_TAC THEN
    `lnpm [(lswapstr pi s, z)] (lnpm pi t) = lnpm pi t`
       by SRW_TAC [][lnpm_fresh, fv_lnpm] THEN
    `~(s IN ctxtFV G)`
       by (IMP_RES_TAC typing_valid_ctxt THEN
           FULL_SIMP_TAC bool_ss [valid_ctxt_CONS] THEN
           FULL_SIMP_TAC (srw_ss()) [ctxtFV_ctxtswap, pmact_decompose] THEN
           FULL_SIMP_TAC (srw_ss()) []) THEN
    `ctxtswap [(lswapstr pi s,z)] (ctxtswap pi G) = ctxtswap pi G`
       by SRW_TAC [][ctxtswap_fresh] THEN
    FULL_SIMP_TAC (srw_ss()) [GSYM pmact_decompose,
                              GSYM ctxtswap_APPEND]
  ]);

val strong_typing_ind = IndDefLib.derive_strong_induction(typing_rules,
                                                          typing_ind)

val typing_cofin_ind = store_thm(
  "typing_cofin_ind",
  ``!P. (!G s ty. valid_ctxt G /\ MEM (s,ty) G ==> P G (var s) ty) /\
        (!G t1 t2 ty1 ty2.
            P G t1 (ty1 --> ty2) /\ P G t2 ty1  ==>
            P G (app t1 t2) ty2) /\
        (!G X t ty1 ty2.
            FINITE X /\
            (!s. ~(s IN X) ==> P ((s,ty1)::G) (open 0 (var s) t) ty2) ==>
            P G (abs t) (ty1 --> ty2))
      ==>
        !G t ty. typing G t ty ==> P G t ty``,
  GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!G t ty. typing G t ty ==>
                           !pi. P (ctxtswap pi G) (lnpm pi t) ty`
        THEN1 METIS_TAC [pmact_nil, ctxtswap_NIL] THEN
  HO_MATCH_MP_TAC strong_typing_ind THEN
  SRW_TAC [][lnpm_open] THEN1 METIS_TAC [] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  Q.EXISTS_TAC `fv (lnpm pi t) UNION ctxtFV (ctxtswap pi G)` THEN
  SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `[(s',lswapstr pi s)] ++ pi` MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  Q_TAC SUFF_TAC `(lnpm ((s', lswapstr pi s)::pi) t = lnpm pi t) /\
                  (ctxtswap ((s',lswapstr pi s)::pi) G = ctxtswap pi G)`
        THEN1 SRW_TAC [][] THEN
  `lnpm [(s',lswapstr pi s)] (lnpm pi t) = lnpm pi t`
      by SRW_TAC [][lnpm_fresh, fv_lnpm] THEN
  FULL_SIMP_TAC (srw_ss()) [GSYM pmact_decompose] THEN
  `~(s IN ctxtFV G)`
      by (IMP_RES_TAC typing_valid_ctxt THEN
          FULL_SIMP_TAC bool_ss [valid_ctxt_CONS]) THEN
  `ctxtswap ((s',lswapstr pi s)::pi) G =
      ctxtswap ([(s',lswapstr pi s)] ++ pi) G`
     by SRW_TAC [][] THEN
  ` _ = ctxtswap [(s',lswapstr pi s)] (ctxtswap pi G)`
     by SRW_TAC [][ctxtswap_APPEND] THEN
  ` _ = ctxtswap pi G`
     by SRW_TAC [][ctxtswap_fresh] THEN
  SRW_TAC [][]);

(* The approach in "Engineering Formal Metatheory" is to define a separate
   "cofinite" relation, to prove the desired properties of this relation, and
   to finish up by showing that it and the original correspond.  *)

val (cotyping_rules, cotyping_ind, cotyping_cases) = Hol_reln`
  (!G s ty. valid_ctxt G /\ MEM (s, ty) G ==> cotyping G (var s) ty) /\
  (!G t1 t2 ty1 ty2.
      cotyping G t1 (ty1 --> ty2) /\ cotyping G t2 ty1 ==>
      cotyping G (app t1 t2) ty2) /\
  (!G X t ty1 ty2.
      FINITE X /\
      (!s. ~(s IN X) ==> cotyping ((s,ty1)::G) (open 0 (var s) t) ty2) ==>
      cotyping G (abs t) (ty1 --> ty2))
`;

val cotyping_typing = store_thm(
  "cotyping_typing",
  ``!G t ty. cotyping G t ty ==> typing G t ty``,
  HO_MATCH_MP_TAC cotyping_ind THEN SRW_TAC [][typing_rules]
    THEN1 METIS_TAC [typing_rules] THEN
  MATCH_MP_TAC (last (CONJUNCTS typing_rules)) THEN
  Q_TAC (NEW_TAC "z") `fv t UNION X` THEN METIS_TAC []);

val typing_cotyping = store_thm(
  "typing_cotyping",
  ``!G t ty. typing G t ty ==> cotyping G t ty``,
  HO_MATCH_MP_TAC typing_cofin_ind THEN SRW_TAC [][cotyping_rules] THEN
  METIS_TAC [cotyping_rules]);

val _ = export_theory();
