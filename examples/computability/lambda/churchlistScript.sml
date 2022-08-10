open HolKernel boolLib bossLib Parse binderLib

open churchnumTheory churchboolTheory
open reductionEval pred_setTheory termTheory chap3Theory
open normal_orderTheory
open head_reductionTheory
open unary_recfnsTheory

val _ = new_theory "churchlist"

val lSYM = MATCH_MP chap2Theory.lameq_SYM

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

Theorem FV_ccons[simp]: FV ccons = {}
Proof csimp[EXTENSION, ccons_def]
QED

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

(* cvlist allows terms to contain HOL lists of terms *)
val cvlist_def = Define`
  cvlist l = FOLDR cvcons cnil l
`;

Theorem cvlist_thm[simp]:
  cvlist [] = cnil ∧
  cvlist (h::t) = cvcons h (cvlist t)
Proof SRW_TAC [][cvlist_def]
QED

val cvcons_eq_ccons =
    wh_ccons |> MATCH_MP (GEN_ALL head_reductionTheory.whstar_lameq)
             |> MATCH_MP chap2Theory.lameq_SYM
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

val cappend_equiv = brackabs.brackabs_equiv [] cappend_def

Theorem FV_cappend[simp]:   FV cappend = {}
Proof SRW_TAC [][EXTENSION, cappend_def] >> metis_tac[]
QED

val wh_cappend = store_thm(
  "wh_cappend",
  ``cappend @@ (ccons @@ h @@ t) @@ l2 -w->* cvcons h (t @@ l2 @@ ccons) ∧
    cappend @@ (cvcons h t) @@ l2 -w->* cvcons h (t @@ l2 @@ ccons) ∧
    cappend @@ cnil @@ l2 -w->* l2``,
  SRW_TAC [][cappend_def,cnil_def] THEN unvarify_tac whstar_substitutive THEN
  ASM_SIMP_TAC (whfy(srw_ss())) [wh_ccons, wh_cvcons, wh_K]);

Theorem cappend_behaviour :
  cappend @@ cvcons h t @@ l2 == cvcons h (cappend @@ t @@ l2)
Proof
  simp_tac (bsrw_ss()) [cappend_equiv, Cong cvcons_cong, wh_cvcons, wh_ccons]
QED

val celbody_def = Define`
  celbody =
  LAM "a" (LAM "r" (LAM "m"
     (cis_zero @@ VAR "m"
               @@ VAR "a"
               @@ (VAR "r" @@ (cpred @@ VAR "m")))))
`;
Theorem FV_celbody[simp]:  FV celbody = {}
Proof
  SRW_TAC [][celbody_def, EXTENSION] >> metis_tac[]
QED

val wh_narg_cis_zero = store_thm(
  "wh_narg_cis_zero",
  ``N -n->* church n ⇒ cis_zero @@ N -w->* cB (n = 0)``,
  SRW_TAC [][cis_zero_def] THEN ASM_SIMP_TAC (whfy(srw_ss())) [] THEN
  FULL_SIMP_TAC (srw_ss()) [church_def] THEN
  Q_TAC (NEW_TAC "z") `FV N ∪ {"z"; "s"}` THEN
  `LAM "z" (LAM "s" (FUNPOW (APP (VAR "s")) n (VAR "z"))) =
   LAM z (LAM "s" (FUNPOW (APP (VAR "s")) n (VAR z)))`
     by SRW_TAC [][LAM_eq_thm] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  `∃N0. N -w->* LAM z N0 ∧ N0 -n->* LAM "s" (FUNPOW (APP (VAR "s")) n (VAR z))`
     by METIS_TAC [normstar_to_abs_wstar] THEN
  ASM_SIMP_TAC (whfy(srw_ss())) [] THEN
  Q_TAC (NEW_TAC "s") `FV N0 ∪ {"s"; z}` THEN
  `LAM "s" (FUNPOW (APP (VAR "s")) n (VAR z)) =
     LAM s (FUNPOW (APP (VAR s)) n (VAR z))`
    by SRW_TAC [][LAM_eq_thm] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  `∃N1. N0 -w->* LAM s N1 ∧ N1 -n->* FUNPOW (APP (VAR s)) n (VAR z)`
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

Theorem FV_cel[simp]:   FV cel = ∅
Proof SRW_TAC [][cel_def, EXTENSION] >> metis_tac[]
QED

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

Theorem cel_def' = MATCH_MP head_reductionTheory.whstar_lameq wh_cel

Theorem cel_correct:
  ∀i l. i < LENGTH l ==> cel @@ church i @@ cvlist l == EL i l
Proof
  Induct_on ‘l’ >> simp[] >>
  Cases_on ‘i’ >> simp_tac (bsrw_ss()) [wh_cel_grnd] >>
  strip_tac >> asm_simp_tac (bsrw_ss()) [lSYM cel_def']
QED

val cmap_def = Define`
  cmap =
  LAM "f" (LAM "l"
    (VAR "l" @@ cnil
             @@ LAM "h" (LAM "r" (ccons @@ (VAR "f" @@ VAR "h") @@ (VAR "r")))))
`;

Theorem FV_cmap[simp]:  FV cmap = ∅
Proof SRW_TAC [][cmap_def, pred_setTheory.EXTENSION] >> metis_tac[]
QED

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

Theorem FV_cfilter[simp]:   FV cfilter = ∅
Proof SRW_TAC [][pred_setTheory.EXTENSION, cfilter_def] >> metis_tac[]
QED

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
  SRW_TAC [][ctabulate_def, pred_setTheory.EXTENSION] >> metis_tac[]);

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
  SRW_TAC [][cmem_def, pred_setTheory.EXTENSION] >> metis_tac[]);

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

val cappend_snoc = store_thm(
  "cappend_snoc",
  ``cappend @@ cvlist l @@ cvcons h cnil == cvlist (l ++ [h])``,
  SIMP_TAC (bsrw_ss()) [cappend_equiv, cnil_def] THEN
  Induct_on `l` THEN
  ASM_SIMP_TAC (bsrw_ss()) [cnil_def, wh_cvcons, wh_ccons]);

val GENLIST_CONS = rich_listTheory.GENLIST_CONS

val cvlist_genlist_cong = store_thm(
  "cvlist_genlist_cong",
  ``(∀x. f x == g x) ⇒
    cvlist (GENLIST f n) == cvlist (GENLIST g n)``,
  MAP_EVERY Q.ID_SPEC_TAC [`g`, `f`] THEN
  Induct_on `n` THEN1 SRW_TAC [][rich_listTheory.GENLIST] THEN
  SRW_TAC [][GENLIST_CONS] THEN
  ASM_SIMP_TAC (bsrw_ss()) [Cong cvcons_cong, combinTheory.o_DEF] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`f o SUC`, `g o SUC`] MP_TAC) THEN
  ASM_SIMP_TAC (bsrw_ss()) [Cong cvcons_cong, combinTheory.o_DEF]);

val ctabulate_cvlist = store_thm(
  "ctabulate_cvlist",
  ``∀f. ctabulate @@ church n @@ f == cvlist (GENLIST (λm. f @@ church m) n)``,
  Induct_on `n` THEN
  ASM_SIMP_TAC (bsrw_ss()) [ctabulate_behaviour, GENLIST_CONS,
                            Cong cvcons_cong, cnil_def] THEN
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
  ``cmap @@ f @@ cvlist l == cvlist (MAP (APP f) l)``,
  Induct_on `l` THEN
  ASM_SIMP_TAC (bsrw_ss()) [cmap_behaviour, Cong cvcons_cong]);

val cmem_cvlist = store_thm(
  "cmem_cvlist",
  ``(∀e. MEM e l ⇒ ∃n. e == church n) ⇒
    cmem @@ church m @@ cvlist l ==
    cB (EXISTS (λt. ceqnat @@ church m @@ t == cB T) l)``,
  Induct_on `l` THEN
  ASM_SIMP_TAC (bsrw_ss()) [cmem_behaviour] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM (Q.SPEC_THEN `h`
                           (STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) [])) THEN
  ASM_SIMP_TAC (bsrw_ss()) [cmem_behaviour, Cong cvcons_cong,
                            churchnumTheory.ceqnat_behaviour] THEN
  Cases_on `m = n` THEN SRW_TAC [][]);

Theorem cappend_cvlist:
  cappend @@ cvlist l1 @@ cvlist l2 == cvlist (l1 ++ l2)
Proof
  Induct_on ‘l1’ >>
  asm_simp_tac (bsrw_ss()) [cappend_behaviour, Cong cvcons_cong] >>
  simp_tac (bsrw_ss())[wh_cappend]
QED

Theorem cvlist_LIST_REL_cong :
  LIST_REL (==) l1 l2 ⇒ cvlist l1 == cvlist l2
Proof
  qid_spec_tac ‘l2’ >> Induct_on ‘l1’ >> simp[PULL_EXISTS] >> rw[] >>
  irule cvcons_cong >> simp[]
QED

val sing_def = Define‘sing = LAM "x" (ccons @@ VAR "x" @@ cnil)’;
Theorem FV_sing[simp]: FV sing = ∅
Proof rw[sing_def, pred_setTheory.EXTENSION]
QED

val sing_eqn = brackabs.brackabs_equiv [] sing_def
Theorem sing_behaviour:
  sing @@ x == cvlist [x]
Proof
  SIMP_TAC (bsrw_ss())[sing_eqn, wh_ccons]
QED

val cogenlist_def = Define‘
  cogenlist =
  LAM "f" (LAM "n" (
     natrec @@ cnil
            @@ (LAM "m"
                 (LAM "r"
                    (cappend @@ VAR "r" @@
                       (VAR "f" @@ VAR "m" @@ cnil @@ sing))))
            @@ VAR "n"
  ))
’;

Theorem FV_cogenlist[simp]:
  FV cogenlist = ∅
Proof SRW_TAC [][cogenlist_def, pred_setTheory.EXTENSION] >> metis_tac[]
QED

val cogenlist_eqn = brackabs.brackabs_equiv [] cogenlist_def

(* would be defined in HOL as
     ogenlist f 0 = [] /\
     ogenlist f (SUC n) =
       ogenlist f n ++
       case f n of NONE => [] | SOME x => [x]
   with type :(num -> 'a option) -> num -> 'a list
*)
Theorem cogenlist_behaviour:
  cogenlist @@ f @@ church 0 == cnil ∧
  cogenlist @@ f @@ church (SUC n) ==
      cappend @@ (cogenlist @@ f @@ church n)
              @@ (f @@ church n @@ cnil @@ sing)
Proof
  SIMP_TAC (bsrw_ss()) [cogenlist_eqn, natrec_behaviour]
QED

Definition cnull_def:
  cnull = LAM "l" (VAR "l" @@ cB T @@ (K @@ (K @@ cB F)))
End

Theorem FV_cnull[simp]: FV cnull = ∅
Proof rw[cnull_def]
QED

val cnull_equiv = brackabs.brackabs_equiv [] cnull_def

Theorem cnull_behaviour:
  cnull @@ cvlist ts == cB (ts = [])
Proof
  Cases_on ‘ts’ >> simp[] >>
  simp_tac (bsrw_ss()) [cnull_equiv, cnil_def, wh_cvcons]
QED

(* ----------------------------------------------------------------------
    fold and unfold
   ---------------------------------------------------------------------- *)

Definition cfold0_def:
  cfold0 =
  LAM "l" (
    VAR "l"
      @@ (cpair @@ church 0 @@ cB T)
      @@ LAM "h" (
           LAM "r" (
             csnd @@ VAR "r"
                  @@ (cpair @@ VAR "h" @@ cB F) (* t was null *)
                  @@ (cpair @@  (cnpair @@ VAR "h" @@ (cfst @@ VAR "r"))
                            @@ cB F)
           )
         )
  )
End

Theorem FV_cfold0[simp]:
  FV cfold0 = ∅
Proof
  rw[cfold0_def, EXTENSION] >> metis_tac[]
QED

Theorem cfold0_equiv = brackabs.brackabs_equiv [] cfold0_def
Theorem cvpr' = churchpairTheory.cpair_behaviour |> MATCH_MP nstar_lameq |> lSYM

Theorem cvpr_cong:
  m1 == m2 ==> n1 == n2 ==> cvpr m1 n1 == cvpr m2 n2
Proof simp_tac (bsrw_ss()) [cvpr']
QED

Theorem equiv_iff:
  ∀m p. (∀n. m:term == n <=> p == n) ==> m == p
Proof metis_tac[chap2Theory.lameq_rules]
QED

val cfold0_ts =
    MATCH_MP equiv_iff
             (SIMP_CONV (bsrw_ss())
                        [cfold0_equiv, churchpairTheory.cpair_behaviour]
                        “cfold0 @@ ts == X” |> Q.GEN ‘X’)

Theorem csnd_cfold0_nullcheck:
  csnd @@ (cfold0 @@ cvlist ts) == cB (ts = [])
Proof
  Induct_on ‘ts’ >> simp_tac(bsrw_ss()) [cfold0_equiv, wh_cvcons, cnil_def] >>
  asm_simp_tac (bsrw_ss()) [lSYM cfold0_ts, churchpairTheory.cpair_behaviour] >>
  Cases_on ‘ts’ >> simp[] >>
  simp_tac (bsrw_ss()) []
QED

val csnd_CONS_case =
    SIMP_RULE (srw_ss()) [] (Q.INST [‘ts’ |-> ‘h::t’]
                                    csnd_cfold0_nullcheck)

Theorem cfold0_behaviour:
  cfold0 @@ cnil == cvpr (church 0) (cB T) ∧
  cfold0 @@ cvcons t cnil == cvpr t (cB F) ∧
  cfold0 @@ cvcons t1 (cvcons t2 (cvlist ts)) ==
    cvpr (cnpair @@ t1 @@ (cfst @@ (cfold0 @@ cvcons t2 (cvlist ts)))) (cB F)
Proof
  rpt conj_tac
  >- simp_tac(bsrw_ss()) [cfold0_equiv, churchpairTheory.cpair_behaviour,
                          wh_cvcons, cnil_def, Cong cvpr_cong]
  >- simp_tac(bsrw_ss()) [cfold0_equiv, churchpairTheory.cpair_behaviour,
                          wh_cvcons, cnil_def, Cong cvpr_cong] >>
  simp_tac(bsrw_ss()) [SimpL “$==”, Once cfold0_equiv] >>
  simp_tac(bsrw_ss()) [Once wh_cvcons, SimpL “$==”] >>
  simp_tac(bsrw_ss()) [lSYM cfold0_ts, churchpairTheory.cpair_behaviour] >>
  simp_tac(bsrw_ss()) [csnd_CONS_case]
QED

Definition cfold_def:
  cfold = B @@ cfst @@ cfold0
End

Theorem FV_cfold[simp]:
  FV cfold = ∅
Proof  rw[cfold_def]
QED

Theorem cfold_behaviour:
  cfold @@ cnil == church 0 ∧
  cfold @@ cvcons t cnil == t ∧
  cfold @@ cvcons t1 (cvcons t2 (cvlist ts)) ==
    cnpair @@ t1 @@ (cfold @@ cvcons t2 (cvlist ts))
Proof
  simp_tac (bsrw_ss()) [SimpL “$==”, cfold_def, cfold0_behaviour] >>
  simp_tac (bsrw_ss()) [cfold_def]
QED

Theorem cfold_correct:
  cfold @@ cvlist (MAP church ns) == church (fold ns)
Proof
  Induct_on ‘ns’ >> simp_tac(bsrw_ss()) [cfold_behaviour] >>
  Cases_on ‘ns’ >> fs[] >> asm_simp_tac(bsrw_ss()) [cfold_behaviour]
QED

Definition cunfold_def:
  cunfold =
  natrec @@ (LAM "m" cnil)
         @@ (LAM "n" (LAM "f" (LAM "m"
                 (cis_zero @@ VAR "n"
                           @@ (ccons @@ VAR "m" @@ cnil)
                           @@ (ccons @@ (cnfst @@ VAR "m")
                                     @@ (VAR "f"
                                             @@ (cnsnd @@ VAR "m")))))))
End

Theorem FV_cunfold[simp]: FV cunfold = ∅
Proof rw[cunfold_def, EXTENSION] >> metis_tac[]
QED

Theorem cunfold_equiv = brackabs.brackabs_equiv [] cunfold_def

Theorem cunfold_behaviour:
  cunfold @@ church 0 @@ z == cnil ∧
  cunfold @@ church (SUC n) @@ m ==
    if n = 0 then cvlist [m]
    else cvcons (cnfst @@ m) (cunfold @@ church n @@ (cnsnd @@ m))
Proof
  simp_tac (bsrw_ss()) [cunfold_equiv, natrec_behaviour] >>
  simp_tac (bsrw_ss()) [lSYM cunfold_equiv] >>
  simp_tac (bsrw_ss()) [wh_ccons] >> rw[] >>
  simp_tac (bsrw_ss()) []
QED

Theorem cunfold_correct:
  ∀n m. cunfold @@ church n @@ church m == cvlist (MAP church (unfold n m))
Proof
  Induct_on ‘n’ >>
  simp_tac (bsrw_ss()) [cunfold_behaviour] >> rw[] >>
  asm_simp_tac (bsrw_ss()) [cnfst_behaviour, Cong cvcons_cong]
QED

val _ = export_theory()
