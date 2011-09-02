open HolKernel bossLib boolLib Parse

open nomsetTheory

val _ = new_theory "contextlists"

val _ = set_trace "Unicode" 1

val _ = type_abbrev("ctxt", ``:(string # 'a) list``)

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

val ctxtFV_APPEND = store_thm(
  "ctxtFV_APPEND",
  ``ctxtFV (G1 ++ G2) = ctxtFV G1 ∪ ctxtFV G2``,
  Induct_on `G1` THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD,
                           pred_setTheory.EXTENSION] THEN
  METIS_TAC []);

val valid_ctxt_APPEND = store_thm(
  "valid_ctxt_APPEND",
  ``valid_ctxt (G1 ++ G2) ==> valid_ctxt G1 ∧ valid_ctxt G2``,
  Induct_on `G1` THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, ctxtFV_APPEND]);

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
  ``ctxtFV (ctxtswap pi G) = setpm string_pmact pi (ctxtFV G)``,
  SRW_TAC [][ctxtFV_MEM, pred_setTheory.EXTENSION] THEN
  METIS_TAC [MEM_ctxtswap, basic_swapTheory.lswapstr_inverse, stringpm_raw]);
val _ = export_rewrites ["ctxtFV_ctxtswap"]


(* valid_ctxt also respects permutation *)
val valid_ctxt_swap0 = prove(
  ``!G. valid_ctxt G ==> !x y. valid_ctxt (ctxtswap pi G)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, stringpm_raw]);

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

(* sub-context relation, overloaded to use SUBSET *)
val subctxt_def = Define`
  subctxt Γ Δ = ∀x A. MEM (x,A) Γ ==> MEM (x,A) Δ
`;
val _ = overload_on("SUBSET", ``subctxt``)

val subctxt_nil = store_thm(
  "subctxt_nil",
  ``[] ⊆ Γ``,
  SRW_TAC [][subctxt_def]);
val _ = export_rewrites ["subctxt_nil"]

val subctxt_refl = store_thm(
  "subctxt_refl",
  ``G : 'a ctxt ⊆ G``,
  SRW_TAC [][subctxt_def]);
val _ = export_rewrites ["subctxt_refl"]

(* cute, but unnecessary *)
val subctxt_ctxtFV = store_thm(
  "subctxt_ctxtFV",
  ``C1 ⊆ C2 ==> ctxtFV C1 ⊆ ctxtFV C2``,
  SIMP_TAC (srw_ss()) [pred_setTheory.SUBSET_DEF, subctxt_def] THEN
  METIS_TAC [ctxtFV_MEM]);

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

val valid_ctxt_FILTER = store_thm(
  "valid_ctxt_FILTER",
  ``valid_ctxt G ==> valid_ctxt (FILTER P G)``,
  Induct_on `G` THEN SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  SRW_TAC [][listTheory.MEM_FILTER, ctxtFV_MEM]);

val domfilter_def = Define`
  domfilter (G:'a ctxt) P = FILTER (λ(x,ty). x ∈ P) G
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
  ``(G:'a ctxt) ∩ P ⊆ G``,
  SRW_TAC [][subctxt_def, domfilter_def, listTheory.MEM_FILTER]);

val domfilter_delete = store_thm(
  "domfilter_delete",
  ``¬(v ∈ ctxtFV G) ==> (G ∩ (s DELETE v) = G ∩ s)``,
  Induct_on `G` THEN SRW_TAC [][]);

val _ = export_theory()
