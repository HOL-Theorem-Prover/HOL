open HolKernel boolLib bossLib Parse dep_rewrite
     pred_setTheory bagTheory helperSetTheory
     monoidTheory monoidMapTheory

(* Theory about folding a monoid (or group) operation over a bag of elements *)

val _ = new_theory"gbag";

(* uses helperSetTheory so cannot move to bagTheory as-is *)
Theorem BAG_OF_SET_IMAGE_INJ:
  !f s.
  (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) ==>
  BAG_OF_SET (IMAGE f s) = BAG_IMAGE f (BAG_OF_SET s)
Proof
  rw[FUN_EQ_THM, BAG_OF_SET, BAG_IMAGE_DEF]
  \\ rw[] \\ gs[GSYM BAG_OF_SET]
  \\ gs[BAG_FILTER_BAG_OF_SET]
  \\ simp[BAG_CARD_BAG_OF_SET]
  >- (
    irule SING_CARD_1
    \\ simp[SING_TEST, GSYM pred_setTheory.MEMBER_NOT_EMPTY]
    \\ metis_tac[] )
  >- simp[EXTENSION]
  \\ qmatch_asmsub_abbrev_tac`INFINITE z`
  \\ `z = {}` suffices_by metis_tac[FINITE_EMPTY]
  \\ simp[EXTENSION, Abbr`z`]
QED

Overload GITBAG = ``\(g:'a monoid) s b. ITBAG g.op s b``;

Theorem GITBAG_THM =
  ITBAG_THM |> CONV_RULE SWAP_FORALL_CONV
  |> INST_TYPE [beta |-> alpha] |> Q.SPEC`(g:'a monoid).op`
  |> GEN_ALL

Theorem GITBAG_EMPTY[simp]:
  !g a. GITBAG g {||} a = a
Proof
  rw[ITBAG_EMPTY]
QED

Theorem GITBAG_INSERT:
  !b. FINITE_BAG b ==>
    !g x a. GITBAG g (BAG_INSERT x b) a =
              GITBAG g (BAG_REST (BAG_INSERT x b))
                (g.op (BAG_CHOICE (BAG_INSERT x b)) a)
Proof
  rw[ITBAG_INSERT]
QED

Theorem SUBSET_COMMUTING_ITBAG_INSERT:
  !f b t.
    SET_OF_BAG b SUBSET t /\ closure_comm_assoc_fun f t /\ FINITE_BAG b ==>
          !x a::t. ITBAG f (BAG_INSERT x b) a = ITBAG f b (f x a)
Proof
  simp[RES_FORALL_THM]
  \\ rpt gen_tac \\ strip_tac
  \\ completeInduct_on `BAG_CARD b`
  \\ rw[]
  \\ simp[ITBAG_INSERT, BAG_REST_DEF, EL_BAG]
  \\ qmatch_goalsub_abbrev_tac`{|c|}`
  \\ `BAG_IN c (BAG_INSERT x b)` by PROVE_TAC[BAG_CHOICE_DEF, BAG_INSERT_NOT_EMPTY]
  \\ fs[BAG_IN_BAG_INSERT]
  \\ `?b0. b = BAG_INSERT c b0` by PROVE_TAC [BAG_IN_BAG_DELETE, BAG_DELETE]
  \\ `BAG_DIFF (BAG_INSERT x b) {| c |} = BAG_INSERT x b0`
  by SRW_TAC [][BAG_INSERT_commutes]
  \\ pop_assum SUBST_ALL_TAC
  \\ first_x_assum(qspec_then`BAG_CARD b0`mp_tac)
  \\ `FINITE_BAG b0` by FULL_SIMP_TAC (srw_ss()) []
  \\ impl_keep_tac >- SRW_TAC [numSimps.ARITH_ss][BAG_CARD_THM]
  \\ disch_then(qspec_then`b0`mp_tac)
  \\ impl_tac >- simp[]
  \\ impl_tac >- fs[SUBSET_DEF]
  \\ impl_tac >- simp[]
  \\ strip_tac
  \\ first_assum(qspec_then`x`mp_tac)
  \\ first_x_assum(qspec_then`c`mp_tac)
  \\ impl_keep_tac >- fs[SUBSET_DEF]
  \\ disch_then(qspec_then`f x a`mp_tac)
  \\ impl_keep_tac >- metis_tac[closure_comm_assoc_fun_def]
  \\ strip_tac
  \\ impl_tac >- simp[]
  \\ disch_then(qspec_then`f c a`mp_tac)
  \\ impl_keep_tac >- metis_tac[closure_comm_assoc_fun_def]
  \\ disch_then SUBST1_TAC
  \\ simp[]
  \\ metis_tac[closure_comm_assoc_fun_def]
QED

Theorem COMMUTING_GITBAG_INSERT:
  !g b. AbelianMonoid g /\ FINITE_BAG b /\ SET_OF_BAG b SUBSET G ==>
  !x a::(G). GITBAG g (BAG_INSERT x b) a = GITBAG g b (g.op x a)
Proof
  rpt strip_tac
  \\ irule SUBSET_COMMUTING_ITBAG_INSERT
  \\ metis_tac[abelian_monoid_op_closure_comm_assoc_fun]
QED

Theorem GITBAG_INSERT_THM =
  SIMP_RULE(srw_ss())[RES_FORALL_THM, PULL_FORALL, AND_IMP_INTRO]
  COMMUTING_GITBAG_INSERT

Theorem GITBAG_UNION:
  !g. AbelianMonoid g ==>
  !b1. FINITE_BAG b1 ==> !b2. FINITE_BAG b2 /\ SET_OF_BAG b1 SUBSET G
                                            /\ SET_OF_BAG b2 SUBSET G ==>
  !a. a IN G ==> GITBAG g (BAG_UNION b1 b2) a = GITBAG g b2 (GITBAG g b1 a)
Proof
  gen_tac \\ strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[]
  \\ simp[BAG_UNION_INSERT]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ gs[SUBSET_DEF]
  \\ simp[GSYM CONJ_ASSOC]
  \\ conj_tac >- metis_tac[]
  \\ first_x_assum irule
  \\ simp[]
  \\ fs[AbelianMonoid_def]
QED

Theorem GITBAG_in_carrier:
  !g. AbelianMonoid g ==>
  !b. FINITE_BAG b ==> !a. SET_OF_BAG b SUBSET G /\ a IN G ==> GITBAG g b a IN G
Proof
  ntac 2 strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ simp[]
  \\ rpt strip_tac
  \\ drule COMMUTING_GITBAG_INSERT
  \\ disch_then (qspec_then`b`mp_tac)
  \\ fs[SUBSET_DEF]
  \\ simp[RES_FORALL_THM, PULL_FORALL]
  \\ strip_tac
  \\ last_x_assum irule
  \\ metis_tac[monoid_op_element, AbelianMonoid_def]
QED

Overload GBAG = ``\(g:'a monoid) b. GITBAG g b g.id``;

Theorem GBAG_in_carrier:
  !g b. AbelianMonoid g /\ FINITE_BAG b /\ SET_OF_BAG b SUBSET G ==> GBAG g b IN G
Proof
  rw[]
  \\ irule GITBAG_in_carrier
  \\ metis_tac[AbelianMonoid_def, monoid_id_element]
QED

Theorem GITBAG_GBAG:
  !g. AbelianMonoid g ==>
  !b. FINITE_BAG b ==> !a. a IN g.carrier /\ SET_OF_BAG b SUBSET g.carrier ==>
      GITBAG g b a = g.op a (GITBAG g b g.id)
Proof
  ntac 2 strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[] >- fs[AbelianMonoid_def]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[]
  \\ conj_asm1_tac >- fs[SUBSET_DEF, AbelianMonoid_def]
  \\ irule EQ_TRANS
  \\ qexists_tac`g.op (g.op e a) (GBAG g b)`
  \\ conj_tac >- (
    first_x_assum irule
    \\ metis_tac[AbelianMonoid_def, monoid_op_element] )
  \\ first_x_assum(qspec_then`e`mp_tac)
  \\ simp[]
  \\ `g.op e (#e) = e` by metis_tac[AbelianMonoid_def, monoid_id]
  \\ pop_assum SUBST1_TAC
  \\ disch_then SUBST1_TAC
  \\ fs[AbelianMonoid_def]
  \\ irule monoid_assoc
  \\ simp[]
  \\ irule GBAG_in_carrier
  \\ simp[AbelianMonoid_def]
QED

Theorem GBAG_UNION:
  AbelianMonoid g /\ FINITE_BAG b1 /\ FINITE_BAG b2 /\
  SET_OF_BAG b1 SUBSET g.carrier /\ SET_OF_BAG b2 SUBSET g.carrier ==>
  GBAG g (BAG_UNION b1 b2) = g.op (GBAG g b1) (GBAG g b2)
Proof
  rpt strip_tac
  \\ DEP_REWRITE_TAC[GITBAG_UNION]
  \\ simp[]
  \\ conj_tac >- fs[AbelianMonoid_def]
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ simp[]
  \\ irule GBAG_in_carrier
  \\ simp[]
QED

Theorem GITBAG_BAG_IMAGE_op:
  !g. AbelianMonoid g ==>
  !b. FINITE_BAG b ==>
  !p q a. IMAGE p (SET_OF_BAG b) SUBSET g.carrier /\
          IMAGE q (SET_OF_BAG b) SUBSET g.carrier /\ a IN g.carrier ==>
  GITBAG g (BAG_IMAGE (\x. g.op (p x) (q x)) b) a =
  g.op (GITBAG g (BAG_IMAGE p b) a) (GBAG g (BAG_IMAGE q b))
Proof
  ntac 2 strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[] >- fs[AbelianMonoid_def]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ conj_asm1_tac
  >- (
    gs[SUBSET_DEF, PULL_EXISTS]
    \\ gs[AbelianMonoid_def] )
  \\ qmatch_goalsub_abbrev_tac`GITBAG g bb aa`
  \\ first_assum(qspecl_then[`p`,`q`,`aa`]mp_tac)
  \\ impl_tac >- (
    fs[SUBSET_DEF, PULL_EXISTS, Abbr`aa`]
    \\ fs[AbelianMonoid_def] )
  \\ simp[]
  \\ disch_then kall_tac
  \\ simp[Abbr`aa`]
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ conj_asm1_tac >- (
    fs[SUBSET_DEF, PULL_EXISTS]
    \\ fs[AbelianMonoid_def] )
  \\ irule EQ_SYM
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ conj_asm1_tac >- fs[AbelianMonoid_def]
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG |> SIMP_RULE(srw_ss())[PULL_FORALL,AND_IMP_INTRO]
                          |> Q.SPECL[`g`,`b`,`g.op x y`]]
  \\ simp[]
  \\ fs[AbelianMonoid_def]
  \\ qmatch_goalsub_abbrev_tac`_ * _ * gp * ( _ * gq)`
  \\ `gp ∈ g.carrier ∧ gq ∈ g.carrier`
  by (
    unabbrev_all_tac
    \\ conj_tac \\ irule GBAG_in_carrier
    \\ fs[AbelianMonoid_def] )
  \\ drule monoid_assoc
  \\ strip_tac \\ gs[]
QED

Theorem IMP_GBAG_EQ_ID:
  AbelianMonoid g ==>
  !b. BAG_EVERY ((=) g.id) b ==> GBAG g b = g.id
Proof
  rw[]
  \\ `FINITE_BAG b`
  by (
    Cases_on`b = {||}` \\ simp[]
    \\ once_rewrite_tac[GSYM unibag_FINITE]
    \\ rewrite_tac[FINITE_BAG_OF_SET]
    \\ `SET_OF_BAG b = {g.id}`
    by (
      rw[SET_OF_BAG, FUN_EQ_THM]
      \\ fs[BAG_EVERY]
      \\ rw[EQ_IMP_THM]
      \\ Cases_on`b` \\ rw[] )
    \\ pop_assum SUBST1_TAC
    \\ simp[])
  \\ qpat_x_assum`BAG_EVERY _ _` mp_tac
  \\ pop_assum mp_tac
  \\ qid_spec_tac`b`
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[] \\ gs[]
  \\ drule COMMUTING_GITBAG_INSERT
  \\ disch_then drule
  \\ impl_keep_tac
  >- (
    fs[SUBSET_DEF, BAG_EVERY]
    \\ fs[AbelianMonoid_def]
    \\ metis_tac[monoid_id_element] )
  \\ simp[RES_FORALL_THM, PULL_FORALL, AND_IMP_INTRO]
  \\ disch_then(qspecl_then[`#e`,`#e`]mp_tac)
  \\ simp[]
  \\ metis_tac[monoid_id_element, monoid_id_id, AbelianMonoid_def]
QED

Theorem GITBAG_CONG:
  !g. AbelianMonoid g ==>
  !b. FINITE_BAG b ==> !b' a a'. FINITE_BAG b' /\
        a IN g.carrier /\ SET_OF_BAG b SUBSET g.carrier /\ SET_OF_BAG b' SUBSET g.carrier
        /\ (!x. BAG_IN x (BAG_UNION b b') /\ x <> g.id ==> b x = b' x)
  ==>
  GITBAG g b a = GITBAG g b' a
Proof
  ntac 2 strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT \\ rw[]
  >- (
    fs[BAG_IN, BAG_INN, EMPTY_BAG]
    \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
    \\ simp[]
    \\ irule EQ_TRANS
    \\ qexists_tac`g.op a g.id`
    \\ conj_tac >- fs[AbelianMonoid_def]
    \\ AP_TERM_TAC
    \\ irule EQ_SYM
    \\ irule IMP_GBAG_EQ_ID
    \\ simp[BAG_EVERY, BAG_IN, BAG_INN]
    \\ metis_tac[])
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[]
  \\ fs[SET_OF_BAG_INSERT]
  \\ Cases_on`e = g.id`
  >- (
    fs[AbelianMonoid_def]
    \\ first_x_assum irule
    \\ simp[]
    \\ fs[BAG_INSERT]
    \\ metis_tac[] )
  \\ `BAG_IN e b'`
  by (
    simp[BAG_IN, BAG_INN]
    \\ fs[BAG_INSERT]
    \\ first_x_assum(qspec_then`e`mp_tac)
    \\ simp[] )
  \\ drule BAG_DECOMPOSE
  \\ disch_then(qx_choose_then`b2`strip_assume_tac)
  \\ pop_assum SUBST_ALL_TAC
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[] \\ fs[SET_OF_BAG_INSERT]
  \\ first_x_assum irule \\ simp[]
  \\ fs[BAG_INSERT, AbelianMonoid_def]
  \\ qx_gen_tac`x`
  \\ disch_then assume_tac
  \\ first_x_assum(qspec_then`x`mp_tac)
  \\ impl_tac >- metis_tac[]
  \\ IF_CASES_TAC \\ simp[]
QED

Theorem GITBAG_same_op:
  g1.op = g2.op ==>
  !b. FINITE_BAG b ==>
  !a. GITBAG g1 b a = GITBAG g2 b a
Proof
  strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[GITBAG_THM]
QED

Theorem GBAG_IMAGE_PARTITION:
  AbelianMonoid g /\ FINITE s ==>
  !b. FINITE_BAG b ==>
    IMAGE f (SET_OF_BAG b) SUBSET G /\
    (!x. BAG_IN x b ==> ?P. P IN s /\ P x) /\
    (!x P1 P2. BAG_IN x b /\ P1 IN s /\ P2 IN s /\ P1 x /\ P2 x ==> P1 = P2)
  ==>
    GBAG g (BAG_IMAGE (λP. GBAG g (BAG_IMAGE f (BAG_FILTER P b))) (BAG_OF_SET s)) =
    GBAG g (BAG_IMAGE f b)
Proof
  strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ simp[]
  \\ conj_tac
  >- (
    irule IMP_GBAG_EQ_ID
    \\ simp[BAG_EVERY]
    \\ rw[]
    \\ imp_res_tac BAG_IN_BAG_IMAGE_IMP
    \\ fs[] )
  \\ rpt strip_tac
  \\ fs[SET_OF_BAG_INSERT]
  \\ `∃P. P IN s /\ P e` by metis_tac[]
  \\ `∃s0. s = P INSERT s0 /\ P NOTIN s0` by metis_tac[DECOMPOSITION]
  \\ BasicProvers.VAR_EQ_TAC
  \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ DEP_REWRITE_TAC[BAG_IMAGE_FINITE_INSERT]
  \\ qpat_x_assum`_ ⇒ _`mp_tac
  \\ impl_tac >- metis_tac[]
  \\ strip_tac
  \\ conj_tac >- metis_tac[FINITE_INSERT, FINITE_BAG_OF_SET]
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE ff (BAG_OF_SET s0)`
  \\ `BAG_IMAGE ff (BAG_OF_SET s0) =
      BAG_IMAGE (\P. GBAG g (BAG_IMAGE f (BAG_FILTER P b))) (BAG_OF_SET s0)`
  by (
    irule BAG_IMAGE_CONG
    \\ simp[Abbr`ff`]
    \\ rw[]
    \\ metis_tac[IN_INSERT] )
  \\ simp[Abbr`ff`]
  \\ pop_assum kall_tac
  \\ rpt(first_x_assum(qspec_then`ARB`kall_tac))
  \\ pop_assum mp_tac
  \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ fs[AbelianMonoid_def]
  \\ conj_asm1_tac >- fs[SUBSET_DEF, PULL_EXISTS]
  \\ conj_asm1_tac >- (
    fs[SUBSET_DEF, PULL_EXISTS]
    \\ rw[] \\ irule GITBAG_in_carrier
    \\ fs[SUBSET_DEF, PULL_EXISTS, AbelianMonoid_def] )
  \\ simp[]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[]
  \\ conj_asm1_tac
  >- (
    simp[AbelianMonoid_def]
    \\ irule GITBAG_in_carrier
    \\ simp[AbelianMonoid_def] )
  \\ simp[]
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG] \\ simp[] \\ strip_tac
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG] \\ simp[]
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG] \\ simp[]
  \\ DEP_REWRITE_TAC[monoid_assoc]
  \\ simp[]
  \\ conj_tac >- ( irule GBAG_in_carrier \\ simp[] )
  \\ irule EQ_SYM
  \\ irule GITBAG_GBAG
  \\ simp[]
QED

Theorem GBAG_PARTITION:
  AbelianMonoid g /\ FINITE s /\ FINITE_BAG b /\ SET_OF_BAG b SUBSET G /\
    (!x. BAG_IN x b ==> ?P. P IN s /\ P x) /\
    (!x P1 P2. BAG_IN x b /\ P1 IN s /\ P2 IN s /\ P1 x /\ P2 x ==> P1 = P2)
  ==>
    GBAG g (BAG_IMAGE (λP. GBAG g (BAG_FILTER P b)) (BAG_OF_SET s)) = GBAG g b
Proof
  strip_tac
  \\ `!P. FINITE_BAG (BAG_FILTER P b)` by metis_tac[FINITE_BAG_FILTER]
  \\ `GBAG g b = GBAG g (BAG_IMAGE I b)` by metis_tac[BAG_IMAGE_FINITE_I]
  \\ pop_assum SUBST1_TAC
  \\ `(λP. GBAG g (BAG_FILTER P b)) = λP. GBAG g (BAG_IMAGE I (BAG_FILTER P b))`
  by simp[FUN_EQ_THM]
  \\ pop_assum SUBST1_TAC
  \\ irule GBAG_IMAGE_PARTITION
  \\ simp[]
  \\ metis_tac[]
QED

Theorem GBAG_IMAGE_FILTER:
  AbelianMonoid g ==>
  !b. FINITE_BAG b ==> IMAGE f (SET_OF_BAG b ∩ P) SUBSET g.carrier ==>
  GBAG g (BAG_IMAGE f (BAG_FILTER P b)) =
  GBAG g (BAG_IMAGE (\x. if P x then f x else g.id) b)
Proof
  strip_tac
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ conj_asm1_tac
  >- (
    rw[]
    \\ fs[monoidTheory.AbelianMonoid_def]
    \\ metis_tac[IN_DEF] )
  \\ irule EQ_SYM
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ fs[monoidTheory.AbelianMonoid_def]
  \\ qmatch_goalsub_abbrev_tac`_ * gg`
  \\ `gg IN g.carrier`
  by (
    simp[Abbr`gg`]
    \\ irule GBAG_in_carrier
    \\ simp[monoidTheory.AbelianMonoid_def, SUBSET_DEF, PULL_EXISTS] )
  \\ IF_CASES_TAC \\ gs[]
  \\ simp[Abbr`gg`]
  \\ irule EQ_SYM
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[PULL_EXISTS, SUBSET_DEF, monoidTheory.AbelianMonoid_def]
  \\ conj_tac >- metis_tac[]
  \\ qpat_x_assum`_ = _`(assume_tac o SYM) \\ simp[]
  \\ irule GITBAG_GBAG
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ metis_tac[monoidTheory.AbelianMonoid_def]
QED

Theorem GBAG_INSERT:
  AbelianMonoid g /\ FINITE_BAG b /\ SET_OF_BAG b SUBSET g.carrier /\ x IN g.carrier ==>
  GBAG g (BAG_INSERT x b) = g.op x (GBAG g b)
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[]
  \\ `Monoid g` by fs[monoidTheory.AbelianMonoid_def] \\ simp[]
  \\ irule GITBAG_GBAG
  \\ simp[]
QED

Theorem MonoidHomo_GBAG:
  AbelianMonoid g /\ AbelianMonoid h /\
  MonoidHomo f g h /\ FINITE_BAG b /\ SET_OF_BAG b SUBSET g.carrier ==>
  f (GBAG g b) = GBAG h (BAG_IMAGE f b)
Proof
  strip_tac
  \\ ntac 2 (pop_assum mp_tac)
  \\ qid_spec_tac`b`
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ simp[]
  \\ fs[MonoidHomo_def]
  \\ rpt strip_tac
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ `GBAG g b IN g.carrier` suffices_by metis_tac[]
  \\ irule GBAG_in_carrier
  \\ simp[SUBSET_DEF, PULL_EXISTS]
QED

Theorem IMP_GBAG_EQ_EXP:
  AbelianMonoid g /\ x IN g.carrier /\ SET_OF_BAG b SUBSET {x} ==>
  GBAG g b = g.exp x (b x)
Proof
  Induct_on`b x` \\ rw[]
  >- (
    Cases_on`b = {||}` \\ simp[]
    \\ fs[SUBSET_DEF]
    \\ Cases_on`b` \\ fs[BAG_INSERT] )
  \\ `b = BAG_INSERT x (b - {|x|})`
  by (
    simp[BAG_EXTENSION]
    \\ simp[BAG_INN, BAG_INSERT, EMPTY_BAG, BAG_DIFF]
    \\ rw[] )
  \\ qmatch_asmsub_abbrev_tac`BAG_INSERT x b0`
  \\ fs[]
  \\ `b0 x = v` by fs[BAG_INSERT]
  \\ first_x_assum(qspecl_then[`b0`,`x`]mp_tac)
  \\ simp[]
  \\ impl_tac >- fs[SUBSET_DEF]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ simp[BAG_INSERT]
  \\ rewrite_tac[GSYM arithmeticTheory.ADD1]
  \\ simp[]
  \\ DEP_REWRITE_TAC[GSYM FINITE_SET_OF_BAG]
  \\ `SET_OF_BAG b0 SUBSET {x}` by fs[SUBSET_DEF]
  \\ `FINITE {x}` by simp[]
  \\ reverse conj_tac >- fs[SUBSET_DEF]
  \\ metis_tac[SUBSET_FINITE]
QED

val _ = export_theory();
