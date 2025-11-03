Theory contextlists
Ancestors
  nomset sorting

Type ctxt = “:(string # 'a) list”

(* permutation over contexts swaps the strings and leaves the types alone *)
Overload ctxtswap = “listpm (pair_pmact string_pmact discrete_pmact)”

(* the free variables of a context *)
Overload ctxtFV =
         “supp (list_pmact (pair_pmact string_pmact discrete_pmact))”

(* A context is valid if the strings
   are all disjoint.  Here's the primitive recursive defn. *)
Definition valid_ctxt_def[simp]:
  (valid_ctxt [] ⇔ T) ∧
  (valid_ctxt ((x,A) :: G) ⇔ x ∉ ctxtFV G ∧ valid_ctxt G)
End

(* here's the alternative characterisation in terms of the standard
   ALL_DISTINCT constant *)
Theorem valid_ctxt_ALL_DISTINCT:
  ∀G. valid_ctxt G = ALL_DISTINCT (MAP FST G)
Proof
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, NOT_IN_supp_listpm,
                           listTheory.MEM_MAP]
QED

Theorem valid_ctxt_APPEND:
  valid_ctxt (G1 ++ G2) ==> valid_ctxt G1 ∧ valid_ctxt G2
Proof
  Induct_on ‘G1’ THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]
QED

(* context membership "respects" permutation *)
Theorem MEM_ctxtswap[simp]:
  !G pi x A. MEM (lswapstr pi x, A) (ctxtswap pi G) = MEM (x,A) G
Proof SRW_TAC [][MEM_listpm]
QED

Theorem ctxtFV_ctxtswap:
   ctxtFV (ctxtswap pi G) = setpm string_pmact pi (ctxtFV G)
Proof
  MATCH_ACCEPT_TAC perm_supp
QED
val _ = export_rewrites ["ctxtFV_ctxtswap"]

(* valid_ctxt also respects permutation *)
val valid_ctxt_swap0 = prove(
  “!G. valid_ctxt G ==> !x y. valid_ctxt (ctxtswap pi G)”,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);

Theorem valid_ctxt_swap:
   valid_ctxt (ctxtswap pi G) = valid_ctxt G
Proof
  METIS_TAC [valid_ctxt_swap0, pmact_inverse]
QED
val _ = export_rewrites ["valid_ctxt_swap"]

(* contexts have finitely many free variables *)
Theorem FINITE_ctxtFV[simp]: FINITE (ctxtFV G)
Proof
  Induct_on ‘G’ >> simp[pairTheory.FORALL_PROD, supp_pairpm]
QED

Theorem ctxtswap_fresh:
   ¬(x ∈ ctxtFV G) /\ ¬(y ∈ ctxtFV G) ==> (ctxtswap [(x,y)] G = G)
Proof
  MATCH_ACCEPT_TAC supp_fresh
QED

(* sub-context relation, overloaded to use SUBSET *)
Definition subctxt_def:
  subctxt Γ Δ = ∀x A. MEM (x,A) Γ ==> MEM (x,A) Δ
End
Overload SUBSET = “subctxt”

Theorem subctxt_nil[simp]: [] ⊆ Γ
Proof SRW_TAC [][subctxt_def]
QED

Theorem subctxt_refl[simp]: G : 'a ctxt ⊆ G
Proof SRW_TAC [][subctxt_def]
QED

(* cute, but unnecessary *)
Theorem subctxt_ctxtFV:
   C1 ⊆ C2 ==> ctxtFV C1 ⊆ ctxtFV C2
Proof
  SIMP_TAC (srw_ss()) [pred_setTheory.SUBSET_DEF, subctxt_def,
                       IN_supp_listpm, pairTheory.EXISTS_PROD] THEN
  METIS_TAC []
QED

val PERM_RULES = LIST_CONJ [Q.SPEC ‘[]’ PERM_REFL,
                            prove(“∀x l1 l2. PERM l1 l2 ==>
                                               PERM (x::l1) (x::l2)”,
                                  SRW_TAC [][]),
                            prove(“∀x y l1 l2. PERM l1 l2 ==>
                                                PERM (x::y::l1) (y::x::l2)”,
                                  SRW_TAC [][PERM_SWAP_AT_FRONT]),
                            PERM_TRANS]
val strong_perm_ind = IndDefLib.derive_strong_induction (PERM_RULES, PERM_IND)

Theorem valid_ctxt_PERM:
   !G1 G2. PERM G1 G2 ==> (valid_ctxt G1 = valid_ctxt G2)
Proof
  HO_MATCH_MP_TAC strong_perm_ind THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, NOT_IN_supp_listpm] THEN
  SRW_TAC [][] THEN METIS_TAC [PERM_MEM_EQ]
QED

Theorem valid_ctxt_FILTER:
   valid_ctxt G ==> valid_ctxt (FILTER P G)
Proof
  Induct_on ‘G’ THEN
  SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, NOT_IN_supp_listpm] THEN
  SRW_TAC [][IN_supp_listpm, pairTheory.EXISTS_PROD, listTheory.MEM_FILTER]
QED
Definition domfilter_def:
  domfilter (G:'a ctxt) P = FILTER (λ(x,ty). x ∈ P) G
End
val _ = overload_on ("INTER", “domfilter”)

Theorem domfilter_thm:
   ([] ∩ P = []) ∧
    ((h :: G) ∩ P = if FST h ∈ P then h :: (G ∩ P) else G ∩ P)
Proof
  Cases_on ‘h’ THEN SRW_TAC [][domfilter_def]
QED
val _ = export_rewrites ["domfilter_thm"]

Theorem valid_ctxt_domfilter:
   valid_ctxt G ==> valid_ctxt (G ∩ P)
Proof
  SRW_TAC [][domfilter_def, valid_ctxt_FILTER]
QED

Theorem IN_ctxtFV_domfilter:
   x ∈ ctxtFV (G ∩ P) ⇔ x ∈ ctxtFV G ∧ x ∈ P
Proof
  Induct_on ‘G’ THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  SRW_TAC [][] THEN METIS_TAC []
QED
val _ = export_rewrites ["IN_ctxtFV_domfilter"]

Theorem MEM_domfilter[simp]:
  MEM (x,ty) (G ∩ P) ⇔ x ∈ P ∧ MEM (x,ty) G
Proof
  SRW_TAC [][domfilter_def, listTheory.MEM_FILTER]
QED

Theorem subctxt_domfilter:
   (G:'a ctxt) ∩ P ⊆ G
Proof
  SRW_TAC [][subctxt_def, domfilter_def, listTheory.MEM_FILTER]
QED

Theorem domfilter_delete:
   ¬(v ∈ ctxtFV G) ==> (G ∩ (s DELETE v) = G ∩ s)
Proof
  Induct_on ‘G’ THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]
QED

