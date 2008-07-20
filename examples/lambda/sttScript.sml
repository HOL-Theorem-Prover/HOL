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

(* more direct characterisation of ctxtFV *)
val ctxtFV_MEM = store_thm(
  "ctxtFV_MEM",
  ``x IN ctxtFV G = (?A. MEM (x,A) G)``,
  Induct_on `G` THEN
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [pairTheory.FORALL_PROD]);

val ctxtFV_ctxtswap = store_thm(
  "ctxtFV_ctxtswap",
  ``ctxtFV (ctxtswap pi G) = setpm lswapstr pi (ctxtFV G)``,
  SRW_TAC [][ctxtFV_MEM, pred_setTheory.EXTENSION] THEN
  METIS_TAC [MEM_ctxtswap, basic_swapTheory.lswapstr_inverse]);
val _ = export_rewrites ["ctxtFV_ctxtswap"]

val ctxtswap_fresh = store_thm(
  "ctxtswap_fresh",
  ``~(x IN ctxtFV G) /\ ~(y IN ctxtFV G) ==> (ctxtswap [(x,y)] G = G)``,
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

val hastype_valid_ctxt = store_thm(
  "hastype_valid_ctxt",
  ``!G m A. G |- m -: A ==> valid_ctxt G``,
  HO_MATCH_MP_TAC hastype_ind THEN SRW_TAC [][]);

val strong_hastype_ind =
    IndDefLib.derive_strong_induction (hastype_rules, hastype_ind)

val hastype_bvc_ind = store_thm(
  "hastype_bvc_ind",
  ``!P fv.
       (!x. FINITE (fv x)) /\
       (!G s A x. valid_ctxt G /\ MEM (s,A) G ==> P G (VAR s) A x) /\
       (!G m n A B x. (!y. P G m (A --> B) y) /\ (!y. P G n A y) ==>
                      P G (m @@ n) B x) /\
       (!G v m A B x. (!y. P ((v,A)::G) m B y) /\
                      ~(v IN fv x) /\ ~(v IN ctxtFV G) ==>
                      P G (LAM v m) (A --> B) x) ==>
       !G m A. G |- m -: A ==> !x. P G m A x``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!G m A. G |- m -: A ==>
                          !x pi. P (ctxtswap pi G) (tpm pi m) A x`
        THEN1 METIS_TAC [tpm_NIL, ctxtswap_NIL] THEN
  HO_MATCH_MP_TAC strong_hastype_ind THEN SRW_TAC [][hastype_rules] THENL [
    METIS_TAC [hastype_rules],
    Q.MATCH_ABBREV_TAC
      `P (ctxtswap pi G) (LAM (lswapstr pi v) (tpm pi m)) (A --> B) c` THEN
    markerLib.RM_ALL_ABBREVS_TAC THEN
    Q_TAC (NEW_TAC "z") `lswapstr pi v INSERT ctxtFV (ctxtswap pi G) UNION
                         FV (tpm pi m) UNION fv c` THEN
    `LAM (lswapstr pi v) (tpm pi m) =
     LAM z (tpm [(z,lswapstr pi v)] (tpm pi m))`
       by SRW_TAC [][tpm_ALPHA] THEN
    SRW_TAC [][GSYM tpm_APPEND] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN
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
    `valid_ctxt ((v,A)::G)` by METIS_TAC [hastype_valid_ctxt] THEN
    `~(v IN ctxtFV G)` by FULL_SIMP_TAC (srw_ss()) [ctxtFV_MEM] THEN
    SRW_TAC [][ctxtswap_fresh]
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

val hastype_lam_inversion = store_thm(
  "hastype_lam_inversion",
  ``~(v IN ctxtFV G) ==>
        (G |- (LAM v M) -: Ty =
          ?Ty1 Ty2. ((v,Ty1)::G) |- M -: Ty2 /\
                    (Ty = Ty1 --> Ty2))``,
  STRIP_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [hastype_cases])) THEN
  SRW_TAC [][LAM_eq_thm] THEN SRW_TAC [][EQ_IMP_THM] THENL [
    `ctxtswap [(v,x)] ((x,A)::G) |- tpm [(v,x)] m -: B`
       by SRW_TAC [][hastype_swap] THEN
    POP_ASSUM MP_TAC THEN
    `valid_ctxt ((x,A)::G)` by METIS_TAC [hastype_valid_ctxt] THEN
    `~(x IN ctxtFV G)` by (FULL_SIMP_TAC (srw_ss()) [] THEN
                           METIS_TAC [ctxtFV_MEM]) THEN
    SRW_TAC [][ctxtswap_fresh],
    METIS_TAC []
  ]);

val weakening = store_thm(
  "weakening",
  ``!G m A. G |- m -: A ==> !D. valid_ctxt D /\ G <= D ==> D |- m -: A``,
  HO_MATCH_MP_TAC hastype_bvc_ind THEN REPEAT CONJ_TAC THEN
  Q.EXISTS_TAC `ctxtFV` THEN SRW_TAC [][] THENL [
    (* var case *) METIS_TAC [hastype_rules, subctxt_def],
    (* app case *) METIS_TAC [hastype_rules],

    (* abs case *)
    MATCH_MP_TAC (last (CONJUNCTS hastype_rules)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][subctxt_def] THEN
    FULL_SIMP_TAC (srw_ss()) [ctxtFV_MEM, subctxt_def]
  ]);

(* prove a cofinite version of the induction principle *)
val hastype_cofin_ind = store_thm(
  "hastype_cofin_ind",
  ``!P.
       (!G s A. valid_ctxt G /\ MEM (s,A) G ==> P G (VAR s) A) /\
       (!G m n A B.
            P G m (A --> B) /\ P G n A ==>
            P G (m @@ n) B) /\
       (!G v m A B X.
            FINITE X /\
            (!y. ~(y IN X) ==> P ((y,A)::G) ([VAR y/v]m) B) ==>
            P G (LAM v m) (A --> B)) ==>
       !G m A. G |- m -: A ==> P G m A``,
  GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!G m A. G |- m -: A ==> !pi. P (ctxtswap pi G) (tpm pi m) A`
        THEN1 METIS_TAC [tpm_NIL, ctxtswap_NIL] THEN
  HO_MATCH_MP_TAC strong_hastype_ind THEN
  SRW_TAC [][] THEN1 METIS_TAC [] THEN
  Q_TAC (NEW_TAC "z") `FV (tpm pi m) UNION ctxtFV (ctxtswap pi G) UNION
                       {x;lswapstr pi x} UNION FV m UNION ctxtFV G` THEN
  `LAM (lswapstr pi x) (tpm pi m) = LAM z (tpm [(z,lswapstr pi x)] (tpm pi m))`
     by SRW_TAC [][tpm_ALPHA] THEN
  SRW_TAC [][] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  Q.EXISTS_TAC `ctxtFV (ctxtswap pi G) UNION FV (tpm pi m) UNION
                {x; z; lswapstr pi x} UNION FV m UNION ctxtFV G` THEN
  SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `(y, lswapstr pi x) :: pi` MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  `~(x IN ctxtFV G)`
     by (`valid_ctxt ((x,A)::G)` by METIS_TAC [hastype_valid_ctxt] THEN
         FULL_SIMP_TAC (srw_ss()) [ctxtFV_MEM]) THEN
  `ctxtswap ((y,lswapstr pi x)::pi) G =
      ctxtswap [(y,lswapstr pi x)] (ctxtswap pi G)`
     by SRW_TAC [][GSYM ctxtswap_APPEND] THEN
  `_ = ctxtswap pi G` by SRW_TAC [][ctxtswap_fresh] THEN
  `[VAR y/z] (tpm [(z,lswapstr pi x)] (tpm pi m)) =
     tpm [(y,z)] (tpm [(z,lswapstr pi x)] (tpm pi m))`
       by SRW_TAC [][fresh_tpm_subst] THEN
  `_ = tpm [(lswapstr [(y,z)] z, lswapstr [(y,z)] (lswapstr pi x))]
           (tpm [(y,z)] (tpm pi m))`
       by SRW_TAC [][Once (GSYM tpm_sing_to_back)] THEN
  `_ = tpm [(y,lswapstr pi x)] (tpm pi m)`
       by SRW_TAC [][tpm_fresh, nomsetTheory.perm_of_is_perm,
                     nomsetTheory.supp_apart] THEN
  SRW_TAC [][GSYM tpm_APPEND]);

(* and a "cofinite" introduction rule for the abstraction case *)
val cofin_hastype_abs_I = store_thm(
  "cofin_hastype_abs_I",
  ``!X v M A B G.
         FINITE X /\
         (!u. ~(u IN X) ==> (u,A)::G |- [VAR u/v]M -: B)
       ==>
         G |- LAM v M -: (A --> B)``,
  REPEAT STRIP_TAC THEN
  Q_TAC (NEW_TAC "z") `X UNION FV M` THEN
  `LAM v M = LAM z ([VAR z/v] M)` by SRW_TAC [][SIMPLE_ALPHA] THEN
  SRW_TAC [][hastype_rules]);

(* this then allows a nice, renaming free proof of weakening *)
val weakening_cofin = prove(
  ``!G m A. G |- m -: A ==> !D. G <= D /\ valid_ctxt D ==> D |- m -: A``,
  HO_MATCH_MP_TAC hastype_cofin_ind THEN
  SRW_TAC [][] THENL [
    METIS_TAC [hastype_rules, subctxt_def],
    METIS_TAC [hastype_rules],
    MATCH_MP_TAC cofin_hastype_abs_I THEN
    Q.EXISTS_TAC `X UNION ctxtFV D` THEN SRW_TAC [][] THEN
    `valid_ctxt ((u,A)::D)` by FULL_SIMP_TAC (srw_ss()) [ctxtFV_MEM] THEN
    `((u,A)::G) <= ((u,A)::D)`
       by FULL_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [subctxt_def] THEN
    SRW_TAC [][]
  ]);


(* ----------------------------------------------------------------------
    A more involved way of doing a similar "universal in the hypothesis"
    thing.
   ---------------------------------------------------------------------- *)

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
                        (v,A) :: Gamma ||- [VAR v/x]m -: B) /\
                   ~(x IN ctxtFV Gamma) ==>
                   Gamma ||- LAM x m -: A --> B)
`;

val hastype2_swap = store_thm(
  "hastype2_swap",
  ``!G m A. G ||- m -: A ==> !pi. ctxtswap pi G ||- tpm pi m -: A``,
  HO_MATCH_MP_TAC hastype2_ind THEN SRW_TAC [][] THENL [
    METIS_TAC [hastype2_rules, MEM_ctxtswap, valid_ctxt_swap],
    METIS_TAC [hastype2_rules],
    MATCH_MP_TAC (last (CONJUNCTS hastype2_rules)) THEN
    SRW_TAC [][tpm_subst_out] THEN
    METIS_TAC [basic_swapTheory.lswapstr_inverse]
  ]);

val IN_ctxtFV_pm = store_thm(
  "IN_ctxtFV_pm",
  ``x IN ctxtFV (ctxtswap pi G) = lswapstr (REVERSE pi) x IN ctxtFV G``,
  Induct_on `G` THEN SRW_TAC [][]);

val hastype2_bvc_ind = store_thm(
  "hastype2_bvc_ind",
  ``!P fv.
      (!x. FINITE (fv x)) /\
      (!G s A x.
         valid_ctxt G /\ MEM (s,A) G ==> P G (VAR s) A x)
         /\
      (!G m n A B x.
          (!y. P G m (A --> B) y) /\
          (!y. P G n A y) ==>
             P G (m @@ n) B x) /\

      (!G m u A B x.
          (!v y. ~(v IN ctxtFV G) ==> P ((v,A)::G) ([VAR v/u] m) B y) /\
          ~(u IN ctxtFV G) /\ ~(u IN fv x)
        ==>
          P G (LAM u m) (A --> B) x)
    ==>
      !G m ty. G ||- m -: ty ==> !x. P G m ty x``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!G m ty. G ||- m -: ty ==>
                           !pi x. P (ctxtswap pi G) (tpm pi m) ty x`
        THEN1 METIS_TAC [tpm_NIL, ctxtswap_NIL] THEN
  HO_MATCH_MP_TAC hastype2_ind THEN
  SRW_TAC [][] THEN1 METIS_TAC [] THEN
  Q.MATCH_ABBREV_TAC `P GG (LAM vv MM) (A --> B) xx` THEN
  Q_TAC (NEW_TAC "z") `{vv} UNION FV MM UNION ctxtFV GG UNION fv xx` THEN
  `LAM vv MM = LAM z (tpm [(z,vv)] MM)`
     by SRW_TAC [][tpm_ALPHA] THEN
  SRW_TAC [][] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss) [tpm_subst] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`lswapstr (REVERSE ((z,vv)::pi)) v`,
                               `(z,vv)::pi`, `y`]
                 MP_TAC) THEN
  ASM_SIMP_TAC (srw_ss()) [basic_swapTheory.lswapstr_APPEND] THEN
  `~(vv IN ctxtFV GG)` by SRW_TAC [][Abbr`vv`, Abbr`GG`] THEN
  `ctxtswap ((z,vv)::pi) G = ctxtswap [(z,vv)] GG`
     by SRW_TAC [][Abbr`GG`, GSYM ctxtswap_APPEND] THEN
  ` _ = GG` by SRW_TAC [][ctxtswap_fresh] THEN
  `tpm ((z,vv)::pi) m = tpm [(z,vv)] MM`
     by SRW_TAC [][Abbr`MM`, GSYM tpm_APPEND] THEN
  SRW_TAC [][] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [IN_ctxtFV_pm,
                            basic_swapTheory.lswapstr_APPEND]);

val hastype2_bvc_ind0 = save_thm(
  "hastype2_bvc_ind0",
  (Q.GEN `P` o Q.GEN `X` o
   SIMP_RULE bool_ss [] o
   Q.SPECL [`\G m ty x. P G m ty`, `\x. X`] o
   INST_TYPE [alpha |-> ``:unit``]) hastype2_bvc_ind)

val hastype2_valid_ctxt = store_thm(
  "hastype2_valid_ctxt",
  ``!G m A. G ||- m -: A ==> valid_ctxt G``,
  HO_MATCH_MP_TAC hastype2_ind THEN SRW_TAC [][] THEN METIS_TAC []);

val hastype_FV = store_thm(
  "hastype_FV",
  ``!G m A. G |- m -: A ==> !v. v IN FV m ==> v IN ctxtFV G``,
  HO_MATCH_MP_TAC hastype_ind THEN SRW_TAC [][] THEN
  METIS_TAC [ctxtFV_MEM]);

val hastype_swap_eqn = store_thm(
  "hastype_swap_eqn",
  ``G |- tpm pi m -: A = ctxtswap (REVERSE pi) G |- m -: A``,
  METIS_TAC [hastype_swap, tpm_inverse, ctxtswap_inverse]);

val hastype2_swap_eqn = store_thm(
  "hastype2_swap_eqn",
  ``G ||- tpm pi m -: A = ctxtswap (REVERSE pi) G ||- m -: A``,
  METIS_TAC [ctxtswap_inverse, hastype2_swap, tpm_inverse]);

val hastype2_hastype = prove(
  ``!G m A. G ||- m -: A ==> G |- m -: A``,
  HO_MATCH_MP_TAC hastype2_ind THEN REPEAT CONJ_TAC THENL [
    (* var case *) SRW_TAC [][hastype_rules],
    (* app case *) METIS_TAC [hastype_rules],
    (* abs case *) METIS_TAC [hastype_rules, lemma14a]
  ]);

val hastype_hastype2 = prove(
  ``!G m A. G |- m -: A ==> G ||- m -: A``,
  Q_TAC SUFF_TAC `!G m A. G |- m -: A ==> !u:one. G ||- m -: A`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC hastype_bvc_ind THEN Q.EXISTS_TAC `\u. {}` THEN
  SRW_TAC [][hastype2_rules] THENL [
    (* app case *) METIS_TAC [hastype2_rules],
    (* abs case; goal with IH is: *)
    MATCH_MP_TAC (last (CONJUNCTS hastype2_rules)) THEN
    SRW_TAC [][] THEN
    Cases_on `v = v'` THEN1 SRW_TAC [][lemma14a] THEN
    (* if v' = v, proof is trivial; rest of tactic is for other case *)
    `~(v' IN FV m)`
         by METIS_TAC [hastype2_hastype, hastype_FV, ctxtFV_def,
                       pairTheory.FST, pred_setTheory.IN_INSERT] THEN
    `[VAR v'/v] m = tpm [(v',v)] m` by SRW_TAC [][fresh_tpm_subst] THEN
    Q_TAC SUFF_TAC
          `(v,A) :: ctxtswap [(v',v)] G ||- m -: A'`
          THEN1 SRW_TAC [][hastype2_swap_eqn] THEN
    SRW_TAC [][ctxtswap_fresh]
  ]);

val hastype_hastype2_eqn = store_thm(
  "hastype_hastype2_eqn",
  ``G |- m -: A = G ||- m -: A``,
  METIS_TAC [hastype2_hastype, hastype_hastype2]);

val _ = export_theory ()
