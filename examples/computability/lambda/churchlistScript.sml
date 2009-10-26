open HolKernel boolLib bossLib Parse binderLib

open churchnumTheory churchboolTheory pure_dBTheory
open reductionEval pred_setTheory termTheory chap3Theory
open normal_orderTheory churchDBTheory
open head_reductionTheory

val _ = new_theory "churchlist"

val _ = set_trace "Unicode" 1
fun Store_thm (trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val ccons_def = Define`
  ccons =
  LAM "h" (LAM "t" (LAM "n" (LAM "c"
    (VAR "c" @@ VAR "h" @@ (VAR "t" @@ VAR "n" @@ VAR "c")))))
`;

val cnil_def = Define`cnil = K`;
val FV_cnil = Store_thm(
  "FV_cnil",
  ``FV cnil = {}``,
  SRW_TAC [][cnil_def]);

val FV_ccons = Store_thm(
  "FV_ccons",
  ``FV ccons = {}``,
  SRW_TAC [][EXTENSION, ccons_def]);

val cvcons_def = Define`
  cvcons h t =
    let n = NEW (FV h ∪ FV t) in
    let c = NEW (FV h ∪ FV t ∪ {n})
    in
        LAM n (LAM c (VAR c @@ h @@ (t @@ VAR n @@ VAR c)))
`;

val FV_cvcons = Store_thm(
  "FV_cvcons",
  ``FV (cvcons h t) = FV h ∪ FV t``,
  SRW_TAC [][cvcons_def, LET_THM] THEN NEW_ELIM_TAC THEN
  SRW_TAC [][] THEN NEW_ELIM_TAC THEN SRW_TAC [][] THEN
  SRW_TAC [][EXTENSION] THEN METIS_TAC []);

val cvcons_fresh = store_thm(
  "cvcons_fresh",
  ``n ∉ FV h ∧ n ∉ FV t ∧ c ∉ FV h ∧ c ∉ FV t ∧ c ≠ n ⇒
    (cvcons h t = LAM n (LAM c (VAR c @@ h @@ (t @@ VAR n @@ VAR c))))``,
  SRW_TAC [][cvcons_def, LET_THM] THEN NEW_ELIM_TAC THEN SRW_TAC [][] THEN
  NEW_ELIM_TAC THEN SRW_TAC [][] THEN
  SRW_TAC [boolSimps.CONJ_ss][LAM_eq_thm, tpm_fresh] THEN
  Cases_on `v = n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `v = c` THEN FULL_SIMP_TAC (srw_ss()) [tpm_fresh]);

val whnf_cvcons = Store_thm(
  "whnf_cvcons",
  ``whnf (cvcons h t)``,
  SIMP_TAC (srw_ss()) [cvcons_def, LET_THM]);

val SUB_cvcons = Store_thm(
  "SUB_cvcons",
  ``[N/v] (cvcons h t) = cvcons ([N/v]h) ([N/v]t)``,
  Q_TAC (NEW_TAC "n") `{v} ∪ FV N ∪ FV h ∪ FV t` THEN
  Q_TAC (NEW_TAC "c") `{v;n} ∪ FV N ∪ FV h ∪ FV t` THEN
  `cvcons h t = LAM n (LAM c (VAR c @@ h @@ (t @@ VAR n @@ VAR c)))`
    by SRW_TAC [][cvcons_fresh] THEN
  `cvcons ([N/v]h) ([N/v]t) =
     LAM n (LAM c (VAR c @@ [N/v]h @@ ([N/v]t @@ VAR n @@ VAR c)))`
    by SRW_TAC [][cvcons_fresh, chap2Theory.NOT_IN_FV_SUB] THEN
  SRW_TAC [][]);

val wh_ccons = store_thm(
  "wh_ccons",
  ``ccons @@ h @@ t -w->* cvcons h t``,
  SRW_TAC [][ccons_def] THEN FRESH_TAC THEN
  `cvcons h t = LAM n (LAM c (VAR c @@ h @@ (t @@ VAR n @@ VAR c)))`
    by SRW_TAC [][cvcons_fresh] THEN
  ASM_SIMP_TAC (whfy(srw_ss())) []);

val wh_cvcons = store_thm(
  "wh_cvcons",
  ``cvcons h t @@ n @@ c -w->* c @@ h @@ (t @@ n @@ c)``,
  unvarify_tac whstar_substitutive THEN
  `cvcons (VAR hs) (VAR ts) =
     LAM ns (LAM cs (VAR cs @@ VAR hs @@ (VAR ts @@ VAR ns @@ VAR cs)))`
    by SRW_TAC [][cvcons_fresh] THEN
  ASM_SIMP_TAC (whfy(srw_ss())) []);

val lameq_sym = List.nth(CONJUNCTS chap2Theory.lam_eq_rules, 2)
val cvcons_eq_ccons =
    wh_ccons |> MATCH_MP (GEN_ALL head_reductionTheory.whstar_lameq)
             |> MATCH_MP lameq_sym
val cvcons_cong = store_thm(
  "cvcons_cong",
  ``M1 == M2 ⇒ N1 == N2 ⇒ cvcons M1 N1 == cvcons M2 N2``,
  SIMP_TAC (bsrw_ss()) [cvcons_eq_ccons]);

val chd_def = Define`
  chd = LAM "l" (VAR "l" @@ church 0 @@ K)
`;

val FV_chd = Store_thm(
  "FV_chd",
  ``FV chd = {}``,
  SRW_TAC [][EXTENSION, chd_def]);

val wh_chd = store_thm(
  "wh_chd",
  ``chd @@ (ccons @@ h @@ t) -w->* h ∧
    chd @@ (cvcons h t) -w->* h``,
  SRW_TAC [][chd_def] THEN unvarify_tac whstar_substitutive THEN
  ASM_SIMP_TAC (whfy(srw_ss())) [wh_ccons, wh_K, wh_cvcons]);

val cappend_def = Define`
  cappend = LAM "l1" (LAM "l2" (VAR "l1" @@ VAR "l2" @@ ccons))
`

val FV_cappend = Store_thm(
  "FV_cappend",
  ``FV cappend = {}``,
  SRW_TAC [][EXTENSION, cappend_def]);

val wh_cappend = store_thm(
  "wh_cappend",
  ``cappend @@ (ccons @@ h @@ t) @@ l2 -w->* cvcons h (t @@ l2 @@ ccons) ∧
    cappend @@ (cvcons h t) @@ l2 -w->* cvcons h (t @@ l2 @@ ccons) ∧
    cappend @@ cnil @@ l2 -w->* l2``,
  SRW_TAC [][cappend_def,cnil_def] THEN unvarify_tac whstar_substitutive THEN
  ASM_SIMP_TAC (whfy(srw_ss())) [wh_ccons, wh_cvcons, wh_K]);

val celbody_def = Define`
  celbody =
  LAM "a" (LAM "r" (LAM "m"
     (cis_zero @@ VAR "m"
               @@ VAR "a"
               @@ (VAR "r" @@ (cpred @@ VAR "m")))))
`;
val FV_celbody = Store_thm(
  "FV_celbody",
  ``FV celbody = {}``,
  SRW_TAC [][celbody_def, EXTENSION]);

val wh_narg_cis_zero = store_thm(
  "wh_narg_cis_zero",
  ``N -n->* church n ⇒ cis_zero @@ N -w->* cB (n = 0)``,
  SRW_TAC [][cis_zero_def] THEN ASM_SIMP_TAC (whfy(srw_ss())) [] THEN
  FULL_SIMP_TAC (srw_ss()) [church_def] THEN
  Q_TAC (NEW_TAC "z") `FV N ∪ {"z"; "s"}` THEN
  `LAM "z" (LAM "s" (FUNPOW ((@@) (VAR "s")) n (VAR "z"))) =
   LAM z (LAM "s" (FUNPOW ((@@) (VAR "s")) n (VAR z)))`
     by SRW_TAC [][LAM_eq_thm] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  `∃N0. N -w->* LAM z N0 ∧ N0 -n->* LAM "s" (FUNPOW ((@@) (VAR "s")) n (VAR z))`
     by METIS_TAC [normstar_to_abs_wstar] THEN
  ASM_SIMP_TAC (whfy(srw_ss())) [] THEN
  Q_TAC (NEW_TAC "s") `FV N0 ∪ {"s"; z}` THEN
  `LAM "s" (FUNPOW ((@@) (VAR "s")) n (VAR z)) =
     LAM s (FUNPOW ((@@) (VAR s)) n (VAR z))`
    by SRW_TAC [][LAM_eq_thm] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  `∃N1. N0 -w->* LAM s N1 ∧ N1 -n->* FUNPOW ((@@) (VAR s)) n (VAR z)`
    by METIS_TAC [normstar_to_abs_wstar] THEN
  ASM_SIMP_TAC (whfy(srw_ss())) [] THEN
  Cases_on `n` THEN
  FULL_SIMP_TAC (srw_ss()) [arithmeticTheory.FUNPOW_SUC] THENL [
    IMP_RES_TAC normstar_to_vheadnullary_wstar THEN
    ASM_SIMP_TAC (whfy(srw_ss())) [],

    IMP_RES_TAC normstar_to_vheadunary_wstar THEN
    ASM_SIMP_TAC (whfy(srw_ss())) []
  ]);

val wh_celbody = store_thm(
  "wh_celbody",
  ``(N -n->* church 0 ⇒ celbody @@ a @@ r @@ N -w->* a) ∧
    ((∃n. N -n->* church n ∧ 0 < n) ⇒
          celbody @@ a @@ r @@ N -w->* r @@ (cpred @@ N))``,
  SRW_TAC [][celbody_def] THENL [
    unvarify_tac whstar_substitutive THEN FRESH_TAC THEN
    IMP_RES_TAC wh_narg_cis_zero THEN
    ASM_SIMP_TAC (whfy(srw_ss())) [wh_cis_zero, tpm_fresh, wh_cB],

    IMP_RES_TAC wh_narg_cis_zero THEN
    Q.MATCH_ABBREV_TAC `ABS @@ a @@ r @@ N -w->* TO` THEN
    Q_TAC (NEW_TAC "rs") `FV a ∪ FV N` THEN
    `(ABS @@ a @@ r @@ N = [r/rs](ABS @@ a @@ VAR rs @@ N)) ∧
     (TO = [r/rs](VAR rs @@ (cpred @@ N)))`
        by SRW_TAC [][Abbr`ABS`, Abbr`TO`, lemma14b] THEN
    NTAC 2 (POP_ASSUM SUBST1_TAC) THEN
    MATCH_MP_TAC whstar_substitutive THEN
    markerLib.UNABBREV_ALL_TAC THEN FRESH_TAC THEN
    ASM_SIMP_TAC (whfy(srw_ss()) ++ ARITH_ss) [tpm_fresh, wh_cB]
  ]);

val cel_def = Define`
  cel =
  LAM "n" (LAM "l"
    (VAR "l" @@ (K @@ church 0) @@ celbody @@ VAR "n"))
`;

val FV_cel = Store_thm(
  "FV_cel",
  ``FV cel = {}``,
  SRW_TAC [][cel_def, EXTENSION]);

val wh_cel_grnd = store_thm(
  "wh_cel_grnd",
  ``cel @@ church 0 @@ (ccons @@ h @@ t) -w->* h ∧
    cel @@ church 0 @@ cvcons h t -w->* h ∧
    (0 < n ⇒
       cel @@ church n @@ (ccons @@ h @@ t) -w->*
       t @@ (K @@ church 0) @@ celbody @@ (cpred @@ church n) ∧
       cel @@ church n @@ cvcons h t -w->*
       t @@ (K @@ church 0) @@ celbody @@ (cpred @@ church n))``,
  SRW_TAC [][cel_def] THEN unvarify_tac whstar_substitutive THEN
  ASM_SIMP_TAC (whfy(bsrw_ss())) [wh_ccons, wh_cvcons, wh_celbody]);

val wh_cel = store_thm(
  "wh_cel",
  ``cel @@ n @@ l -w->* l @@ (K @@ church 0) @@ celbody @@ n``,
  SRW_TAC [][cel_def] THEN unvarify_tac whstar_substitutive THEN
  ASM_SIMP_TAC (whfy(srw_ss())) []);


val cel_example = prove(
  ``cel @@ church 2
        @@ (cappend @@ (ccons @@ h1 @@ (ccons @@ h2 @@ cnil))
                    @@ (ccons @@ h3 @@ XXX)) -w->*
    h3``,
  unvarify_tac whstar_substitutive THEN
  ASM_SIMP_TAC (whfy(bsrw_ss())) [wh_celbody, wh_ccons, wh_cvcons,
                                  cpred_behaviour, cnil_def, wh_cel,
                                  wh_cappend, wh_K]);

val cmap_def = Define`
  cmap =
  LAM "f" (LAM "l"
    (VAR "l" @@ cnil
             @@ LAM "h" (LAM "r" (ccons @@ (VAR "f" @@ VAR "h") @@ (VAR "r")))))
`;

val FV_cmap = Store_thm(
  "FV_cmap",
  ``FV cmap = {}``,
  SRW_TAC [][cmap_def, pred_setTheory.EXTENSION]);

val cmap_eqn = brackabs.brackabs_equiv [] cmap_def

val cmap_behaviour = store_thm(
  "cmap_behaviour",
  ``cmap @@ f @@ cnil == cnil ∧
    cmap @@ f @@ cvcons h t == cvcons (f @@ h) (cmap @@ f @@ t)``,
  SIMP_TAC (bsrw_ss()) [cmap_eqn, Cong cvcons_cong, cnil_def, wh_cvcons,
                        wh_ccons]);

val cfilter_def = Define`
  cfilter =
  LAM "P" (LAM "l"
    (VAR "l" @@ cnil
             @@ LAM "h" (LAM "r" (VAR "P" @@ VAR "h"
                                          @@ (ccons @@ VAR "h" @@ VAR "r")
                                          @@ VAR "r"))))
`;

val FV_cfilter = Store_thm(
  "FV_cfilter",
  ``FV cfilter = {}``,
  SRW_TAC [][pred_setTheory.EXTENSION, cfilter_def]);

val cfilter_eqn = brackabs.brackabs_equiv [] cfilter_def

val cfilter_behaviour = store_thm(
  "cfilter_behaviour",
  ``cfilter @@ P @@ cnil == cnil ∧
    cfilter @@ P @@ cvcons h t ==
       P @@ h @@ (cvcons h (cfilter @@ P @@ t))
              @@ (cfilter @@ P @@ t)``,
  SIMP_TAC (bsrw_ss()) [cfilter_eqn, cnil_def, wh_cvcons, wh_ccons,
                        Cong cvcons_cong]);

val ctabulate_def = Define`
  ctabulate =
  LAM "n" (LAM "g"
    (VAR "n" @@ (LAM "f" cnil)
             @@ (LAM "r" (LAM "f"
                   (ccons @@ (VAR "f" @@ church 0)
                          @@ (VAR "r" @@ (B @@ VAR "f" @@ csuc)))))
             @@ VAR "g"))
`;

val FV_ctabulate = Store_thm(
  "FV_ctabulate",
  ``FV ctabulate = {}``,
  SRW_TAC [][ctabulate_def, pred_setTheory.EXTENSION]);

val ctabulate_eqn = brackabs.brackabs_equiv [] ctabulate_def

val ctabulate_behaviour = store_thm(
  "ctabulate_behaviour",
  ``ctabulate @@ church 0 @@ f == cnil ∧
    ctabulate @@ (church (SUC n)) @@ f ==
      cvcons (f @@ church 0) (ctabulate @@ church n @@ (B @@ f @@ csuc))``,
  SIMP_TAC (bsrw_ss()) [ctabulate_eqn, cnil_def, Cong cvcons_cong,
                        church_thm, wh_ccons])

val cmem_def = Define`
  cmem =
  LAM "n" (LAM "L"
    (VAR "L"
         @@ cB F
         @@ (LAM "h" (LAM "r" (cor @@ (ceqnat @@ VAR "h" @@ VAR "n")
                                   @@ VAR "r")))))
`;

val FV_cmem = Store_thm(
  "FV_cmem",
  ``FV cmem = {}``,
  SRW_TAC [][cmem_def, pred_setTheory.EXTENSION]);

val cmem_eqn = brackabs.brackabs_equiv [] cmem_def

val cmem_behaviour = store_thm(
  "cmem_behaviour",
  ``cmem @@ N @@ cnil == cB F ∧
    cmem @@ church n @@ cvcons (church m) t ==
      if n = m then cB T
      else cmem @@ church n @@ t``,
  SIMP_TAC (bsrw_ss()) [cmem_eqn, Cong cvcons_cong, cnil_def,
                        wh_cvcons, ceqnat_behaviour] THEN
  SRW_TAC [][] THEN1 SIMP_TAC (bsrw_ss()) [cor_T1] THEN
  SIMP_TAC (bsrw_ss()) [cmem_eqn, cor_F1]);

(* cvlist allows terms to contain HOL lists of terms *)
val cvlist_def = Define`
  cvlist l = FOLDR cvcons cnil l
`;

val cvlist_thm = Store_thm(
  "cvlist_thm",
  ``(cvlist [] = cnil) ∧
    (cvlist (h::t) = cvcons h (cvlist t))``,
  SRW_TAC [][cvlist_def]);

val GENLIST_ALT = store_thm(
  "GENLIST_ALT",
  ``GENLIST f (SUC n) = f 0 :: GENLIST (f o SUC) n``,
  SIMP_TAC std_ss [rich_listTheory.GENLIST_APPEND, arithmeticTheory.ADD1] THEN
  SIMP_TAC bool_ss [rich_listTheory.GENLIST, arithmeticTheory.ONE] THEN
  SRW_TAC [][rich_listTheory.SNOC] THEN
  Q_TAC SUFF_TAC `(λt. f (t + 1)) = f o SUC` THEN1 SRW_TAC [][] THEN
  SRW_TAC [][FUN_EQ_THM, arithmeticTheory.ADD1]);

val cvlist_genlist_cong = store_thm(
  "cvlist_genlist_cong",
  ``(∀x. f x == g x) ⇒
    cvlist (GENLIST f n) == cvlist (GENLIST g n)``,
  MAP_EVERY Q.ID_SPEC_TAC [`g`, `f`] THEN
  Induct_on `n` THEN1 SRW_TAC [][rich_listTheory.GENLIST] THEN
  SRW_TAC [][GENLIST_ALT] THEN
  ASM_SIMP_TAC (bsrw_ss()) [Cong cvcons_cong, combinTheory.o_DEF] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`f o SUC`, `g o SUC`] MP_TAC) THEN
  ASM_SIMP_TAC (bsrw_ss()) [Cong cvcons_cong, combinTheory.o_DEF]);

val ctabulate_cvlist = store_thm(
  "ctabulate_cvlist",
  ``∀f. ctabulate @@ church n @@ f == cvlist (GENLIST (λm. f @@ church m) n)``,
  Induct_on `n` THEN
  ASM_SIMP_TAC (bsrw_ss()) [ctabulate_behaviour, GENLIST_ALT,
                            Cong cvcons_cong, cnil_def]
    THEN1 SRW_TAC [][rich_listTheory.GENLIST, cnil_def] THEN
  GEN_TAC THEN MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] cvcons_cong) THEN
  SRW_TAC [][] THEN
  HO_MATCH_MP_TAC cvlist_genlist_cong THEN
  SIMP_TAC (bsrw_ss()) [churchnumTheory.csuc_behaviour]);

val cfilter_cvlist = store_thm(
  "cfilter_cvlist",
  ``(∀e. MEM e l ⇒ ∃b. P @@ e == cB b) ⇒
      cfilter @@ P @@ cvlist l == cvlist (FILTER (λt. P @@ t == cB T) l)``,
  Induct_on `l` THEN ASM_SIMP_TAC (bsrw_ss()) [cfilter_behaviour] THEN
  SRW_TAC [][] THENL [
    ASM_SIMP_TAC (bsrw_ss()) [churchboolTheory.cB_behaviour] THEN
    MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] cvcons_cong) THEN
    SRW_TAC [][],
    `∃b. P @@ h == cB b` by METIS_TAC [] THEN
    `b ≠ T` by (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []) THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    ASM_SIMP_TAC (bsrw_ss()) [churchboolTheory.cB_behaviour]
  ]);

val cmap_cvlist = store_thm(
  "cmap_cvlist",
  ``cmap @@ f @@ cvlist l == cvlist (MAP ((@@) f) l)``,
  Induct_on `l` THEN
  ASM_SIMP_TAC (bsrw_ss()) [cmap_behaviour, Cong cvcons_cong]);

val _ = export_theory()
