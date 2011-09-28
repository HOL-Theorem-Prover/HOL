open HolKernel boolLib bossLib Parse

open termTheory sttTheory contextlistsTheory NEWLib nomsetTheory

val _ = new_theory "sttVariants"

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
        THEN1 METIS_TAC [pmact_nil] THEN
  HO_MATCH_MP_TAC hastype_strongind THEN
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
         FULL_SIMP_TAC (srw_ss()) []) THEN
  `ctxtswap ((y,lswapstr pi x)::pi) G =
      ctxtswap [(y,lswapstr pi x)] (ctxtswap pi G)`
     by SRW_TAC [][GSYM pmact_decompose] THEN
  `_ = ctxtswap pi G` by SRW_TAC [][ctxtswap_fresh] THEN
  `[VAR y/z] (tpm [(z,lswapstr pi x)] (tpm pi m)) =
     tpm [(y,z)] (tpm [(z,lswapstr pi x)] (tpm pi m))`
       by SRW_TAC [][fresh_tpm_subst] THEN
  `_ = tpm [(lswapstr [(y,z)] z, lswapstr [(y,z)] (lswapstr pi x))]
           (tpm [(y,z)] (tpm pi m))`
       by SRW_TAC [][Once (GSYM pmact_sing_to_back)] THEN
  `_ = tpm [(y,lswapstr pi x)] (tpm pi m)`
       by SRW_TAC [][tpm_fresh, nomsetTheory.supp_apart] THEN
  SRW_TAC [][GSYM pmact_decompose]);

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
  ``!G m A. G |- m -: A ==> !D. G ⊆ D /\ valid_ctxt D ==> D |- m -: A``,
  HO_MATCH_MP_TAC hastype_cofin_ind THEN
  SRW_TAC [][] THENL [
    METIS_TAC [hastype_rules, subctxt_def],
    METIS_TAC [hastype_rules],
    MATCH_MP_TAC cofin_hastype_abs_I THEN
    Q.EXISTS_TAC `X UNION ctxtFV D` THEN SRW_TAC [][] THEN
    `valid_ctxt ((u,A)::D)` by FULL_SIMP_TAC (srw_ss()) [] THEN
    `((u,A)::G) ⊆ ((u,A)::D)`
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
                        (v,A) :: Gamma ||- [VAR v/x]m -: B) ∧
                   ~(x ∈ ctxtFV Gamma) ==>
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
    METIS_TAC [pmact_inverse]
  ]);

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
        THEN1 METIS_TAC [pmact_nil] THEN
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
  ASM_SIMP_TAC (srw_ss()) [pmact_decompose] THEN
  `~(vv IN ctxtFV GG)` by SRW_TAC [][Abbr`vv`, Abbr`GG`] THEN
  `ctxtswap ((z,vv)::pi) G = ctxtswap [(z,vv)] GG`
     by SRW_TAC [][Abbr`GG`, GSYM pmact_decompose] THEN
  ` _ = GG` by SRW_TAC [][ctxtswap_fresh] THEN
  `tpm ((z,vv)::pi) m = tpm [(z,vv)] MM`
     by SRW_TAC [][Abbr`MM`, GSYM pmact_decompose] THEN
  SRW_TAC [][] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [pmact_decompose]);

val hastype2_bvc_ind0 = save_thm(
  "hastype2_bvc_ind0",
  (Q.GEN `P` o Q.GEN `X` o
   SIMP_RULE bool_ss [] o
   Q.SPECL [`\G m ty x. P G m ty`, `\x. X`]) hastype2_bvc_ind)

val hastype2_valid_ctxt = store_thm(
  "hastype2_valid_ctxt",
  ``!G m A. G ||- m -: A ==> valid_ctxt G``,
  HO_MATCH_MP_TAC hastype2_ind THEN SRW_TAC [][] THEN METIS_TAC []);

val hastype2_swap_eqn = store_thm(
  "hastype2_swap_eqn",
  ``G ||- tpm pi m -: A <=> ctxtswap (REVERSE pi) G ||- m -: A``,
  METIS_TAC [hastype2_swap, pmact_inverse]);

val hastype2_hastype = prove(
  ``!G m A. G ||- m -: A ==> G |- m -: A``,
  HO_MATCH_MP_TAC hastype2_ind THEN REPEAT CONJ_TAC THENL [
    (* var case *) SRW_TAC [][hastype_rules],
    (* app case *) METIS_TAC [hastype_rules],
    (* abs case *) METIS_TAC [hastype_rules, lemma14a]
  ]);

val hastype_hastype2 = prove(
  ``!G m A. G |- m -: A ==> G ||- m -: A``,
  HO_MATCH_MP_TAC hastype_indX THEN Q.EXISTS_TAC `{}` THEN
  SRW_TAC [][hastype2_rules] THENL [
    (* app case *) METIS_TAC [hastype2_rules],
    (* abs case; goal with IH is: *)
    MATCH_MP_TAC (last (CONJUNCTS hastype2_rules)) THEN
    SRW_TAC [][] THEN
    Cases_on `v = v'` THEN1 SRW_TAC [][lemma14a] THEN
    (* if v' = v, proof is trivial; rest of tactic is for other case *)
    `v' ∉ ctxtFV ((v,A)::G)` by SRW_TAC [][] THEN
    `~(v' IN FV m)` by METIS_TAC [hastype_FV] THEN
    `[VAR v'/v] m = tpm [(v',v)] m` by SRW_TAC [][fresh_tpm_subst] THEN
    SRW_TAC [][hastype2_swap_eqn, ctxtswap_fresh]
  ]);

val hastype_hastype2_eqn = store_thm(
  "hastype_hastype2_eqn",
  ``G |- m -: A <=> G ||- m -: A``,
  METIS_TAC [hastype2_hastype, hastype_hastype2]);

val _ = export_theory ()
