(* reasoning problems suggested by Randy Pollack:
     1. showing a weakening result for a typing relation over lambda calculus
        terms.  The typing is that of simple type theory.
     2. showing that another relation, one with a universally quantified
        hypothesis, is equivalent to the original.
*)

open HolKernel boolLib Parse bossLib

open ncLib metisLib BasicProvers

open swapTheory ncTheory

val _ = new_theory "stt";

(* define simple types, the "funspace" constructor will get to be written
   as infix "-->".
*)
val _ = Hol_datatype `stype = base | funspace of stype => stype`;

val _ = add_infix("-->", 700, RIGHT)
val _ = overload_on("-->", ``funspace``)

(* a context is a list of string-type pairs, and is valid if the strings
   are all disjoint.  Here's the primitive recursive defn. *)
val valid_ctxt_def = Define`
  (valid_ctxt [] = T) /\
  (valid_ctxt ((x,A) :: G) = (!A'. ~MEM (x, A') G) /\ valid_ctxt G)
`;
val _ = export_rewrites ["valid_ctxt_def"]

(* here's the alternative characterisation in terms of the standard
   ALL_DISTINCT constant *)
val valid_ctxt_ALL_DISTINCT = store_thm(
  "valid_ctxt_ALL_DISTINCT",
  ``!G. valid_ctxt G = ALL_DISTINCT (MAP FST G)``,
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, listTheory.MEM_MAP]);

(* permutation over contexts swaps the strings and leaves the types alone *)
val ctxtswap_def = Define`
  (ctxtswap x y [] = []) /\
  (ctxtswap x y (sA :: G) = (swapstr x y (FST sA), SND sA) :: ctxtswap x y G)
`;
val _ = export_rewrites ["ctxtswap_def"]

val ctxtswap_involution = store_thm(
  "ctxtswap_involution",
  ``ctxtswap x y (ctxtswap x y G) = G``,
  Induct_on `G` THEN SRW_TAC [][]);
val _ = export_rewrites ["ctxtswap_involution"]

(* context membership "respects" permutation *)
val MEM_ctxtswap = store_thm(
  "MEM_ctxtswap",
  ``!G u v x A. MEM (swapstr u v x, A) (ctxtswap u v G) = MEM (x,A) G``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);
val _ = export_rewrites ["MEM_ctxtswap"]

(* valid_ctxt also respects permutation *)
val valid_ctxt_swap0 = prove(
  ``!G. valid_ctxt G ==> !x y. valid_ctxt (ctxtswap x y G)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);
val valid_ctxt_swap = store_thm(
  "valid_ctxt_swap",
  ``valid_ctxt (ctxtswap x y G) = valid_ctxt G``,
  METIS_TAC [valid_ctxt_swap0, ctxtswap_involution]);
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

(* more direct characterisation of ctxtFV *)
val ctxtFV_MEM = store_thm(
  "ctxtFV_MEM",
  ``x IN ctxtFV G = (?A. MEM (x,A) G)``,
  Induct_on `G` THEN
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [pairTheory.FORALL_PROD]);

val ctxtFV_ctxtswap = store_thm(
  "ctxtFV_ctxtswap",
  ``ctxtFV (ctxtswap x y G) = swapset x y (ctxtFV G)``,
  SRW_TAC [][ctxtFV_MEM, pred_setTheory.EXTENSION] THEN
  METIS_TAC [MEM_ctxtswap, swapstr_def]);
val _ = export_rewrites ["ctxtFV_ctxtswap"]

val ctxtswap_fresh = store_thm(
  "ctxtswap_fresh",
  ``~(x IN ctxtFV G) /\ ~(y IN ctxtFV G) ==> (ctxtswap x y G = G)``,
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
  ``!G m ty. G |- m -: ty ==> !x y. ctxtswap x y G |- swap x y m -: ty``,
  HO_MATCH_MP_TAC hastype_ind THEN SRW_TAC [][swap_thm] THENL [
    METIS_TAC [valid_ctxt_swap, MEM_ctxtswap, hastype_rules],
    METIS_TAC [hastype_rules],
    METIS_TAC [hastype_rules, MEM_ctxtswap]
  ]);

(* sub-context relation, overloaded to use <= *)
val subctxt_def = Define`
  subctxt gamma delta = !x A. MEM (x,A) gamma ==> MEM (x,A) delta
`;
val _ = overload_on("<=", ``subctxt``)

(* cute, but unnecessary *)
val subctxt_ctxtFV = store_thm(
  "subctxt_ctxtFV",
  ``C1 <= C2 ==> ctxtFV C1 SUBSET ctxtFV C2``,
  SIMP_TAC (srw_ss()) [pred_setTheory.SUBSET_DEF, subctxt_def] THEN
  METIS_TAC [ctxtFV_MEM]);

val hastype_valid_ctxt = store_thm(
  "hastype_valid_ctxt",
  ``!G m A. G |- m -: A ==> valid_ctxt G``,
  HO_MATCH_MP_TAC hastype_ind THEN SRW_TAC [][]);

val strong_hastype_ind =
    IndDefRules.derive_strong_induction (CONJUNCTS hastype_rules,
                                         hastype_ind)

val weakening = store_thm(
  "weakening",
  ``!G m A. G |- m -: A ==> !D. valid_ctxt D /\ G <= D ==> D |- m -: A``,
  HO_MATCH_MP_TAC strong_hastype_ind THEN REPEAT CONJ_TAC THENL [
    (* var case *) METIS_TAC [hastype_rules, subctxt_def],
    (* app case *) METIS_TAC [hastype_rules],

    (* abs case *)
    (* restatement of goal (with IH etc)  *)
    Q_TAC SUFF_TAC
          `!G v m A B.
              (v,A) :: G |- m -: B /\
              (!D. valid_ctxt D /\ ((v,A)::G) <= D ==> D |- m -: B) ==>
              !D. valid_ctxt D /\ G <= D ==> D |- LAM v m -: A --> B`
          THEN1 METIS_TAC [] THEN REPEAT STRIP_TAC THEN
    (* first invent a fresh z *)
    Q_TAC (NEW_TAC "z") `{v} UNION ctxtFV D UNION FV m` THEN
    `LAM v m = LAM z (swap z v m)`
       by SRW_TAC [][swap_ALPHA] THEN
    Q_TAC SUFF_TAC
          `(z,A)::D |- swap z v m -: B`
          THEN1 METIS_TAC [hastype_rules] THEN
    `(z,A)::D = ctxtswap z v ((v,A)::ctxtswap z v D)` by SRW_TAC [][] THEN
    Q_TAC SUFF_TAC
          `(v,A)::ctxtswap z v D |- m -: B`
          THEN1 METIS_TAC [hastype_swap] THEN
    Q_TAC SUFF_TAC
          `valid_ctxt ((v,A)::ctxtswap z v D) /\
           ((v,A)::G) <= ((v,A)::ctxtswap z v D)`
          THEN1 METIS_TAC [] THEN
    `valid_ctxt ((v,A)::ctxtswap z v D)`
          by (SRW_TAC [][] THEN
              METIS_TAC [MEM_ctxtswap, ctxtFV_MEM, swapstr_def]) THEN
    Q_TAC SUFF_TAC
          `!y B'. MEM (y,B') G ==> MEM (y,B') (ctxtswap z v D)`
          THEN1 (SRW_TAC [][subctxt_def] THEN METIS_TAC []) THEN
    REPEAT STRIP_TAC THEN
    Q_TAC SUFF_TAC
          `~(y = z) /\ ~(y = v)`
          THEN1 METIS_TAC [swapstr_def, MEM_ctxtswap, subctxt_def] THEN
    `~(v IN ctxtFV G)` by METIS_TAC [hastype_valid_ctxt, valid_ctxt_def,
                                     ctxtFV_MEM] THEN
    METIS_TAC [subctxt_def, ctxtFV_MEM]
  ]);


(* now a slightly different typing relation, with different syntax: "||-"
   instead of "|-".  Underlying name of constant is "hastype2".  *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 425),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "||-", BreakSpace(1, 0),
                                 BeginFinalBlock(PP.INCONSISTENT, 2),
                                 TM, HardSpace 1, TOK "-:", BreakSpace(1,0)],
                  term_name = "hastype2"}

val (hastype2_rules, hastype2_ind, hastype2_cases) = Hol_reln`
  (!Gamma s A. valid_ctxt Gamma /\ MEM (s,A) Gamma ==>
               Gamma ||- VAR s -: A) /\
  (!Gamma m n A B. Gamma ||- m -: A --> B /\ Gamma ||- n -: A ==>
                   Gamma ||- m @@ n -: B) /\
  (!Gamma m x A B. (!v. ~(v IN ctxtFV Gamma) ==>
                        (v,A) :: Gamma ||- [VAR v/x]m -: B) ==>
                   Gamma ||- LAM x m -: A --> B)
`;

val hastype2_swap = store_thm(
  "hastype2_swap",
  ``!G m A. G ||- m -: A ==> !x y. ctxtswap x y G ||- swap x y m -: A``,
  HO_MATCH_MP_TAC hastype2_ind THEN SRW_TAC [][swap_thm] THENL [
    METIS_TAC [hastype2_rules, MEM_ctxtswap, valid_ctxt_swap],
    METIS_TAC [hastype2_rules],
    MATCH_MP_TAC (last (CONJUNCTS hastype2_rules)) THEN
    SRW_TAC [][swap_subst_out, swap_thm] THEN
    METIS_TAC [swapstr_def]
  ]);

val hastype2_valid_ctxt = store_thm(
  "hastype2_valid_ctxt",
  ``!G m A. G ||- m -: A ==> valid_ctxt G``,
  HO_MATCH_MP_TAC hastype2_ind THEN SRW_TAC [][] THEN
  Q_TAC (NEW_TAC "z") `ctxtFV G` THEN METIS_TAC []);

val hastype_FV = store_thm(
  "hastype_FV",
  ``!G m A. G |- m -: A ==> !v. v IN FV m ==> v IN ctxtFV G``,
  HO_MATCH_MP_TAC hastype_ind THEN SRW_TAC [][] THEN
  METIS_TAC [ctxtFV_MEM]);

val hastype_swap_eqn = store_thm(
  "hastype_swap_eqn",
  ``G |- swap x y m -: A = ctxtswap x y G |- m -: A``,
  METIS_TAC [hastype_swap, swap_inverse, ctxtswap_involution]);

val hastype2_swap_eqn = store_thm(
  "hastype2_swap_eqn",
  ``G ||- swap x y m -: A = ctxtswap x y G ||- m -: A``,
  METIS_TAC [ctxtswap_involution, hastype2_swap, swap_inverse]);

val hastype2_hastype = prove(
  ``!G m A. G ||- m -: A ==> G |- m -: A``,
  HO_MATCH_MP_TAC hastype2_ind THEN REPEAT CONJ_TAC THENL [
    (* var case *) SRW_TAC [][hastype_rules],
    (* app case *) METIS_TAC [hastype_rules],
    (* abs case; first state the goal, with IH etc *)
    Q_TAC SUFF_TAC
          `!G m x A B.
              (!v. ~(v IN ctxtFV G) ==> (v,A) :: G |- [VAR v/x] m -: B) ==>
              G |- LAM x m -: A --> B` THEN1 METIS_TAC [] THEN
    REPEAT STRIP_TAC THEN
    (* fresh z *)
    Q_TAC (NEW_TAC "z") `FV m UNION ctxtFV G UNION {x}` THEN
    `LAM x m = LAM z ([VAR z/x] m)`
       by SRW_TAC [][SIMPLE_ALPHA] THEN
    METIS_TAC [hastype_rules]
  ]);

val hastype_hastype2 = prove(
  ``!G m A. G |- m -: A ==> G ||- m -: A``,
  HO_MATCH_MP_TAC hastype_ind THEN REPEAT CONJ_TAC THENL [
    (* var case *) SRW_TAC [][hastype2_rules],
    (* app case *) METIS_TAC [hastype2_rules],
    (* abs case; goal with IH is: *)
    Q_TAC SUFF_TAC
          `!G x m A B. (x,A) :: G ||- m -: B ==> G ||- LAM x m -: A --> B`
          THEN1 METIS_TAC [] THEN REPEAT STRIP_TAC THEN
    Q_TAC SUFF_TAC
          `!v. ~(v IN ctxtFV G) ==> (v,A)::G ||- [VAR v/x] m -: B`
          THEN1 METIS_TAC [hastype2_rules] THEN REPEAT STRIP_TAC THEN
    Cases_on `v = x` THEN1 SRW_TAC [][lemma14a] THEN
    (* if v = x, proof is trivial; rest of tactic is for other case *)
    `~(v IN FV m)`
         by METIS_TAC [hastype2_hastype, hastype_FV, ctxtFV_def,
                       pairTheory.FST, pred_setTheory.IN_INSERT] THEN
    `~(x IN ctxtFV G)`
         by METIS_TAC [hastype2_valid_ctxt, valid_ctxt_def, ctxtFV_MEM] THEN
    `[VAR v/x] m = swap v x m` by SRW_TAC [][fresh_var_swap] THEN
    Q_TAC SUFF_TAC
          `(x,A) :: ctxtswap v x G ||- m -: B`
          THEN1 SRW_TAC [][hastype2_swap_eqn] THEN
    SRW_TAC [][ctxtswap_fresh]
  ]);

val hastype_hastype2_eqn = store_thm(
  "hastype_hastype2_eqn",
  ``G |- m -: A = G ||- m -: A``,
  METIS_TAC [hastype2_hastype, hastype_hastype2]);

val _ = export_theory ()
