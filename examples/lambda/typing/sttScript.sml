(* reasoning problems (mainly suggested by Randy Pollack):
     1. showing a weakening result for a typing relation over lambda calculus
        terms.  The typing is that of simple type theory.

        1a. demonstrate that Randy's cofinite approach from POPL2008
            works just as well on this example, saving us from having
            to define a whole other relation in order to get slicker
            proofs.

     2. showing that another relation, one with a universally quantified
        hypothesis, is equivalent to the original.
*)

open HolKernel boolLib Parse bossLib
open binderLib metisLib termTheory;

val export_rewrites = BasicProvers.export_rewrites "stt";

val _ = new_theory "stt";

val _ = set_trace "Unicode" 1

(* define simple types, the "funspace" constructor will get to be written
   as infix "-->".
*)
val _ = Hol_datatype `stype = base | funspace of stype => stype`;

val _ = add_infix("-->", 700, RIGHT)
val _ = overload_on("-->", ``funspace``)

(* a context is a list of string-type pairs *)
val _ = type_abbrev("ctxt", ``:(string # stype) list``)

(* the free variables of a context, defined with primitive recursion to
   give us nice rewrites *)
val ctxtFV_def = Define`
  (ctxtFV [] = {}) /\
  (ctxtFV (h::t) = FST h INSERT ctxtFV t)
`;
val _ = export_rewrites ["ctxtFV_def"]

(* more direct characterisation of ctxtFV *)
val ctxtFV_MEM = store_thm(
  "ctxtFV_MEM",
  ``x ∈ ctxtFV G = (∃A. MEM (x,A) G)``,
  Induct_on `G` THEN
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [pairTheory.FORALL_PROD]);


(* A context is valid if the strings
   are all disjoint.  Here's the primitive recursive defn. *)
val valid_ctxt_def = Define`
  (valid_ctxt [] = T) ∧
  (valid_ctxt ((x,A) :: G) = ¬(x ∈ ctxtFV G) ∧ valid_ctxt G)
`;
val _ = export_rewrites ["valid_ctxt_def"]

(* here's the alternative characterisation in terms of the standard
   ALL_DISTINCT constant *)
val valid_ctxt_ALL_DISTINCT = store_thm(
  "valid_ctxt_ALL_DISTINCT",
  ``∀G. valid_ctxt G = ALL_DISTINCT (MAP FST G)``,
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, ctxtFV_MEM,
                           listTheory.MEM_MAP]);

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
  Induct_on `G` THEN SRW_TAC [][basic_swapTheory.lswapstr_APPEND]);

(* context membership "respects" permutation *)
val MEM_ctxtswap = store_thm(
  "MEM_ctxtswap",
  ``!G pi x A. MEM (lswapstr pi x, A) (ctxtswap pi G) = MEM (x,A) G``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);
val _ = export_rewrites ["MEM_ctxtswap"]

val ctxtFV_ctxtswap = store_thm(
  "ctxtFV_ctxtswap",
  ``ctxtFV (ctxtswap pi G) = setpm lswapstr pi (ctxtFV G)``,
  SRW_TAC [][ctxtFV_MEM, pred_setTheory.EXTENSION] THEN
  METIS_TAC [MEM_ctxtswap, basic_swapTheory.lswapstr_inverse]);
val _ = export_rewrites ["ctxtFV_ctxtswap"]


(* valid_ctxt also respects permutation *)
val valid_ctxt_swap0 = prove(
  ``!G. valid_ctxt G ==> !x y. valid_ctxt (ctxtswap pi G)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);

val valid_ctxt_swap = store_thm(
  "valid_ctxt_swap",
  ``valid_ctxt (ctxtswap pi G) = valid_ctxt G``,
  METIS_TAC [valid_ctxt_swap0, ctxtswap_inverse]);
val _ = export_rewrites ["valid_ctxt_swap"]

(* contexts have finitely many free variables *)
val FINITE_ctxtFV = store_thm(
  "FINITE_ctxtFV",
  ``FINITE (ctxtFV G)``,
  Induct_on `G` THEN SRW_TAC [][]);
val _ = export_rewrites ["FINITE_ctxtFV"]

val ctxtswap_fresh = store_thm(
  "ctxtswap_fresh",
  ``¬(x ∈ ctxtFV G) /\ ¬(y ∈ ctxtFV G) ==> (ctxtswap [(x,y)] G = G)``,
  Induct_on `G` THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);

(* set up parsing/pretty-printing for the typing relation.
   Can't use ":" to the right of the turnstile, because it's already taken
   for HOL's typing, so use "-:" instead, which is ugly. *)

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 425),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "|-", BreakSpace(1, 0),
                                 BeginFinalBlock(PP.INCONSISTENT, 2),
                                 TM, HardSpace 1, TOK "-:", BreakSpace(1,0)],
                  term_name = "hastype"}

(* inductive definition of typing relation *)
val (hastype_rules, hastype_ind, hastype_cases) = Hol_reln`
  (!Gamma s A. valid_ctxt Gamma /\ MEM (s,A) Gamma ==>
               Gamma |- VAR s -: A) /\
  (!Gamma m n A B. Gamma |- m -: A --> B /\ Gamma |- n -: A ==>
                   Gamma |- m @@ n -: B) /\
  (!Gamma x m A B. (x,A) :: Gamma |- m -: B ==>
                   Gamma |- LAM x m -: A --> B)
`;

(* typing relation respects permutation *)
val hastype_swap = store_thm(
  "hastype_swap",
  ``!G m ty. G |- m -: ty ==> !pi. ctxtswap pi G |- tpm pi m -: ty``,
  HO_MATCH_MP_TAC hastype_ind THEN SRW_TAC [][] THENL [
    METIS_TAC [valid_ctxt_swap, MEM_ctxtswap, hastype_rules],
    METIS_TAC [hastype_rules],
    METIS_TAC [hastype_rules, MEM_ctxtswap]
  ]);

val hastype_swap_eqn = store_thm(
  "hastype_swap_eqn",
  ``G |- tpm pi m -: A = ctxtswap (REVERSE pi) G |- m -: A``,
  METIS_TAC [hastype_swap, tpm_inverse, ctxtswap_inverse]);


val hastype_valid_ctxt = store_thm(
  "hastype_valid_ctxt",
  ``!G m A. G |- m -: A ==> valid_ctxt G``,
  HO_MATCH_MP_TAC hastype_ind THEN SRW_TAC [][]);

val strong_hastype_ind = save_thm(
  "strong_hastype_ind",
  IndDefLib.derive_strong_induction (hastype_rules, hastype_ind))

val hastype_bvc_ind = store_thm(
  "hastype_bvc_ind",
  ``!P fv.
       (!x. FINITE (fv x)) /\
       (!G s A x. valid_ctxt G /\ MEM (s,A) G ==> P G (VAR s) A x) /\
       (!G m n A B x.
          (!y. P G m (A --> B) y) /\ (!y. P G n A y) /\
          G |- m -: A --> B ∧ G |- n -: A
        ==>
          P G (m @@ n) B x) /\
       (!G v m A B x. (!y. P ((v,A)::G) m B y) /\
                      ¬(v ∈ fv x) /\ ~(v IN ctxtFV G) ∧
                      (v,A) :: G |- m -: B
                    ==>
                      P G (LAM v m) (A --> B) x) ==>
       !G m A. G |- m -: A ==> !x. P G m A x``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!G m A. G |- m -: A ==>
                          !x pi. P (ctxtswap pi G) (tpm pi m) A x`
        THEN1 METIS_TAC [tpm_NIL, ctxtswap_NIL] THEN
  HO_MATCH_MP_TAC strong_hastype_ind THEN SRW_TAC [][hastype_rules] THENL [
    METIS_TAC [hastype_rules, hastype_swap],
    Q.MATCH_ABBREV_TAC
      `P (ctxtswap pi G) (LAM (lswapstr pi v) (tpm pi m)) (A --> B) c` THEN
    markerLib.RM_ALL_ABBREVS_TAC THEN
    Q_TAC (NEW_TAC "z") `lswapstr pi v INSERT ctxtFV (ctxtswap pi G) UNION
                         FV (tpm pi m) UNION fv c` THEN
    `LAM (lswapstr pi v) (tpm pi m) =
     LAM z (tpm [(z,lswapstr pi v)] (tpm pi m))`
       by SRW_TAC [][tpm_ALPHA] THEN
    SRW_TAC [][GSYM tpm_APPEND] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    `valid_ctxt ((v,A)::G)` by METIS_TAC [hastype_valid_ctxt] THEN
    `~(v IN ctxtFV G)` by FULL_SIMP_TAC (srw_ss()) [ctxtFV_MEM] THEN
    SRW_TAC [][] THENL [
      Q_TAC SUFF_TAC
         `((z,A)::ctxtswap pi G =
           (lswapstr ([(z,lswapstr pi v)] ++ pi) v,A)::
           ctxtswap ([(z,lswapstr pi v)] ++ pi) G) /\
          (tpm ((z,lswapstr pi v)::pi) m = tpm ([(z,lswapstr pi v)] ++ pi) m)`
         THEN1
           (DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC) THEN
            FIRST_X_ASSUM MATCH_ACCEPT_TAC) THEN
      SRW_TAC [][GSYM basic_swapTheory.lswapstr_APPEND,
                 ctxtswap_APPEND] THEN
      SRW_TAC [][ctxtswap_fresh],
      SRW_TAC [][hastype_swap_eqn, basic_swapTheory.lswapstr_APPEND,
                 ctxtswap_APPEND, ctxtswap_fresh]
    ]
  ]);

val all_fnone = prove(
  ``(!(f:one -> 'a). P f) = !x:'a. P (K x)``,
  SRW_TAC [][EQ_IMP_THM] THEN
  Q_TAC SUFF_TAC `f = K (f())`
        THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][]) THEN
  SRW_TAC [][FUN_EQ_THM, oneTheory.one]);


val hastype_indX = save_thm(
  "hastype_indX",
  (Q.GEN `P` o Q.GEN `X` o SIMP_RULE bool_ss [] o
   SPECL [``(λG:ctxt M:term t:stype x:one. P G M t : bool)``,
          ``λx:one. X:string set``] o
   INST_TYPE [alpha |-> ``:one``]) hastype_bvc_ind)

(* sub-context relation, overloaded to use SUBSET *)
val subctxt_def = Define`
  subctxt Γ Δ = ∀x A. MEM (x,A) Γ ==> MEM (x,A) Δ
`;
val _ = overload_on("SUBSET", ``subctxt``)

(* cute, but unnecessary *)
val subctxt_ctxtFV = store_thm(
  "subctxt_ctxtFV",
  ``C1 ⊆ C2 ==> ctxtFV C1 ⊆ ctxtFV C2``,
  SIMP_TAC (srw_ss()) [pred_setTheory.SUBSET_DEF, subctxt_def] THEN
  METIS_TAC [ctxtFV_MEM]);

val hastype_lam_inv = store_thm(
  "hastype_lam_inv",
  ``¬(v ∈ ctxtFV Γ) ==>
        (Γ |- LAM v M -: Ty =
          ∃Ty1 Ty2. ((v,Ty1) :: Γ) |- M -: Ty2 ∧
                    (Ty = Ty1 --> Ty2))``,
  STRIP_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [hastype_cases])) THEN
  SRW_TAC [][LAM_eq_thm] THEN SRW_TAC [][EQ_IMP_THM] THENL [
    `ctxtswap [(v,x)] ((x,A) :: Γ) |- tpm [(v,x)] m -: B`
       by SRW_TAC [][hastype_swap] THEN
    POP_ASSUM MP_TAC THEN
    `valid_ctxt ((x,A):: Γ)` by METIS_TAC [hastype_valid_ctxt] THEN
    `¬(x ∈ ctxtFV Γ)` by (FULL_SIMP_TAC (srw_ss()) [] THEN
                           METIS_TAC [ctxtFV_MEM]) THEN
    SRW_TAC [][ctxtswap_fresh],
    METIS_TAC []
  ]);

val hastype_var_inv = store_thm(
  "hastype_var_inv",
  ``G |- VAR v -: A = MEM (v,A) G ∧ valid_ctxt G``,
  ONCE_REWRITE_TAC [hastype_cases] THEN SRW_TAC [][] THEN METIS_TAC []);
val _ = export_rewrites ["hastype_var_inv"]

val hastype_app_inv = store_thm(
  "hastype_app_inv",
  ``G |- M @@ N -: A = ∃B. G |- M -: B --> A ∧ G |- N -: B``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [hastype_cases])) THEN
  SRW_TAC [][]);

val weakening = store_thm(
  "weakening",
  ``∀G m A. G |- m -: A ==> ∀D. valid_ctxt D ∧ G ⊆ D ==> D |- m -: A``,
  HO_MATCH_MP_TAC hastype_bvc_ind THEN REPEAT CONJ_TAC THEN
  Q.EXISTS_TAC `ctxtFV` THEN SRW_TAC [][] THENL [
    (* var case *) METIS_TAC [hastype_rules, subctxt_def],
    (* app case *) METIS_TAC [hastype_rules],

    (* abs case *)
    SRW_TAC [][hastype_lam_inv] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][subctxt_def] THEN
    FULL_SIMP_TAC (srw_ss()) [subctxt_def]
  ]);

open sortingTheory
val PERM_RULES = LIST_CONJ [Q.SPEC `[]` PERM_REFL,
                            prove(``∀x l1 l2. PERM l1 l2 ==>
                                               PERM (x::l1) (x::l2)``,
                                  SRW_TAC [][]),
                            prove(``∀x y l1 l2. PERM l1 l2 ==>
                                                PERM (x::y::l1) (y::x::l2)``,
                                  SRW_TAC [][PERM_SWAP_AT_FRONT]),
                            PERM_TRANS]

val strong_perm_ind = IndDefLib.derive_strong_induction (PERM_RULES, PERM_IND)

val valid_ctxt_PERM = store_thm(
  "valid_ctxt_PERM",
  ``!G1 G2. PERM G1 G2 ==> (valid_ctxt G1 = valid_ctxt G2)``,
  HO_MATCH_MP_TAC strong_perm_ind THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  SRW_TAC [][] THEN METIS_TAC [PERM_MEM_EQ, ctxtFV_MEM]);

val permutation = store_thm(
  "permutation",
  ``∀G m A. G |- m -: A ==> ∀G'. PERM G G' ==> G' |- m -: A``,
  HO_MATCH_MP_TAC hastype_bvc_ind THEN Q.EXISTS_TAC `ctxtFV` THEN
  SRW_TAC [][] THENL [
    METIS_TAC [PERM_MEM_EQ],
    METIS_TAC [valid_ctxt_PERM],
    SRW_TAC [][hastype_app_inv] THEN METIS_TAC [],
    SRW_TAC [][hastype_lam_inv]
  ]);

val valid_ctxt_FILTER = store_thm(
  "valid_ctxt_FILTER",
  ``valid_ctxt G ==> valid_ctxt (FILTER P G)``,
  Induct_on `G` THEN SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  SRW_TAC [][listTheory.MEM_FILTER, ctxtFV_MEM]);

val domfilter_def = Define`
  domfilter (G:ctxt) P = FILTER (λ(x,ty). x ∈ P) G
`;
val _ = overload_on ("INTER", ``domfilter``)

val domfilter_thm = store_thm(
  "domfilter_thm",
  ``([] ∩ P = []) ∧
    ((h :: G) ∩ P = if FST h ∈ P then h :: (G ∩ P) else G ∩ P)``,
  Cases_on `h` THEN SRW_TAC [][domfilter_def])
val _ = export_rewrites ["domfilter_thm"]

val valid_ctxt_domfilter = store_thm(
  "valid_ctxt_domfilter",
  ``valid_ctxt G ==> valid_ctxt (G ∩ P)``,
  SRW_TAC [][domfilter_def, valid_ctxt_FILTER]);

val IN_ctxtFV_domfilter = store_thm(
  "IN_ctxtFV_domfilter",
  ``x ∈ ctxtFV (G ∩ P) = x ∈ ctxtFV G ∧ x ∈ P``,
  Induct_on `G` THEN SRW_TAC [][] THEN
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss ++ boolSimps.CONJ_ss)
               [EQ_IMP_THM]);
val _ = export_rewrites ["IN_ctxtFV_domfilter"]

val MEM_domfilter = store_thm(
  "MEM_domfilter",
  ``MEM (x,ty) (G ∩ P) = x ∈ P ∧ MEM (x,ty) G``,
  SRW_TAC [][domfilter_def, listTheory.MEM_FILTER]);
val _ = export_rewrites ["MEM_domfilter"]

val subctxt_domfilter = store_thm(
  "subctxt_domfilter",
  ``(G:ctxt) ∩ P ⊆ G``,
  SRW_TAC [][subctxt_def, domfilter_def, listTheory.MEM_FILTER]);

val domfilter_delete = store_thm(
  "domfilter_delete",
  ``¬(v ∈ ctxtFV G) ==> (G ∩ (s DELETE v) = G ∩ s)``,
  Induct_on `G` THEN SRW_TAC [][]);

val strengthening_FV = store_thm(
  "strengthening_FV",
  ``∀G m A. G |- m -: A ==> G ∩ FV m |- m -: A``,
  HO_MATCH_MP_TAC hastype_indX THEN Q.EXISTS_TAC `{}` THEN
  SRW_TAC [][valid_ctxt_domfilter, domfilter_delete] THENL [
    SRW_TAC [][hastype_app_inv] THEN Q.EXISTS_TAC `A` THEN
    `valid_ctxt G` by METIS_TAC [hastype_valid_ctxt] THEN
    `valid_ctxt (G ∩ (FV m ∪ FV m'))`
       by SRW_TAC [][valid_ctxt_domfilter] THEN
    Q_TAC SUFF_TAC
      `G ∩ FV m ⊆ G ∩ (FV m ∪ FV m') ∧ G ∩ FV m' ⊆ G ∩ (FV m ∪ FV m')`
      THEN1 METIS_TAC [weakening] THEN
    SRW_TAC [][subctxt_def],

    SRW_TAC [][hastype_lam_inv],

    SRW_TAC [][hastype_lam_inv] THEN
    `valid_ctxt ((v,A) :: (G ∩ FV m))`
       by METIS_TAC[hastype_valid_ctxt, valid_ctxt_def, IN_ctxtFV_domfilter] THEN
    `(G ∩ FV m) ⊆ ((v,A) :: (G ∩ FV m))`
        by SRW_TAC [][subctxt_def] THEN
    METIS_TAC [weakening]
  ]);

val hastype_FV = store_thm(
  "hastype_FV",
  ``!G m A. G |- m -: A ==> !v. v IN FV m ==> v IN ctxtFV G``,
  HO_MATCH_MP_TAC hastype_ind THEN SRW_TAC [][] THEN
  METIS_TAC [ctxtFV_MEM]);

(* Preservation of typing under β-reduction *)
val typing_sub0 = prove(
  ``∀t vGt' v G A B t'.
      (vGt' = (v,G,t')) ∧
      (v,A) :: G |- t -: B ∧
      G |- t' -: A
    ==>
      G |- [t'/v]t -: B``,
  HO_MATCH_MP_TAC chap3Theory.strong_bvc_term_ind THEN
  Q.EXISTS_TAC `λ(v,G,t'). {v} ∪ ctxtFV G ∪ FV t'` THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  SRW_TAC [][SUB_THM, SUB_VAR, hastype_app_inv, hastype_lam_inv] THENL [
    SRW_TAC [][],
    FULL_SIMP_TAC (srw_ss()) [ctxtFV_MEM],
    METIS_TAC [],
    Q.MATCH_ABBREV_TAC `(v,α) :: Γ |- [M/u]N -: β` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    markerLib.RM_ALL_ABBREVS_TAC THEN
    `Γ ⊆ (v,α) :: Γ`  by SRW_TAC [][subctxt_def] THEN
    METIS_TAC [PERM_SWAP_AT_FRONT, PERM_REFL, permutation, weakening,
               hastype_valid_ctxt, valid_ctxt_def]
  ]);

val typing_sub = save_thm(
  "typing_sub",
  SIMP_RULE (srw_ss()) [] typing_sub0);

open chap3Theory
val preservation = store_thm(
  "preservation",
  ``∀t t'. compat_closure beta t t' ==>
           ∀G A. G |- t -: A ==> G |- t' -: A``,
  HO_MATCH_MP_TAC (GEN_ALL ccbeta_gen_ind) THEN
  Q.EXISTS_TAC `ctxtFV` THEN
  SRW_TAC [][hastype_app_inv, hastype_lam_inv] THENL [
    METIS_TAC [typing_sub],
    METIS_TAC [],
    METIS_TAC []
  ]);

val _ = export_theory ()
