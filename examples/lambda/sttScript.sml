(* a reasoning problem suggested by Randy Pollack:
     showing a weakening result for a typing relation over lambda calculus
     terms.  The typing is that of simple type theory.
*)

open HolKernel boolLib Parse bossLib

open ncLib metisLib BasicProvers

open swapTheory

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
  (valid_ctxt (xA :: G) = (!A'. ~MEM (FST xA, A') G) /\
                          valid_ctxt G)
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
  Induct THEN SRW_TAC [][]);
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
  (!Gamma x m A B. (!A'. ~MEM (x,A') Gamma) /\ (x,A) :: Gamma |- m -: B ==>
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


val weakening = store_thm(
  "weakening",
  ``!G m A. G |- m -: A ==> !D. valid_ctxt D /\ G <= D ==> D |- m -: A``,
  HO_MATCH_MP_TAC hastype_ind THEN REPEAT CONJ_TAC THENL [
    (* var case *) METIS_TAC [hastype_rules, subctxt_def],
    (* app case *) METIS_TAC [hastype_rules],

    (* abs case *)
    (* restatement of goal (with IH etc)  *)
    Q_TAC SUFF_TAC
          `!G v m A B.
              (!A. ~MEM (v,A) G) /\
              (!D. valid_ctxt D /\ ((v,A)::G) <= D ==> D |- m -: B) ==>
              !D. valid_ctxt D /\ G <= D ==> D |- LAM v m -: A --> B`
          THEN1 METIS_TAC [] THEN REPEAT STRIP_TAC THEN
    (* first invent a fresh z *)
    Q_TAC (NEW_TAC "z") `{v} UNION ctxtFV D UNION FV m` THEN
    `LAM v m = LAM z (swap z v m)`
       by SRW_TAC [][swap_ALPHA] THEN
    Q_TAC SUFF_TAC
          `(z,A)::D |- swap z v m -: B /\ (!A. ~MEM (z,A) D)`
          THEN1 METIS_TAC [hastype_rules] THEN
    `!A. ~MEM (z,A) D` by METIS_TAC [ctxtFV_MEM] THEN
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
          `G <= ctxtswap z v D`
          THEN1 (SRW_TAC [][subctxt_def] THEN METIS_TAC []) THEN
    Q_TAC SUFF_TAC
          `!y B. MEM (y,B) G ==> MEM (y,B) (ctxtswap z v D)`
          THEN1 SRW_TAC [][subctxt_def] THEN REPEAT STRIP_TAC THEN
    Q_TAC SUFF_TAC
          `~(y = z)`
          THEN1 METIS_TAC [swapstr_def, MEM_ctxtswap, subctxt_def] THEN
    METIS_TAC [subctxt_def, ctxtFV_MEM]
  ]);

val _ = export_theory ()
