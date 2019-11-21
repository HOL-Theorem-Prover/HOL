open HolKernel Parse boolLib bossLib;

open transferTheory finite_mapTheory pred_setTheory

val _ = new_theory "fsets";

Type fset = “:'a |-> unit”

Overload fIN = “\e (fs:'a fset). e IN FDOM fs”

Overload fUNION = “FUNION : 'a fset -> 'a fset -> 'a fset”

Overload fINSERT = “λe fs. fs |+ (e,())”

Definition FSET_def:
  FSET AB fs s <=> !a b. AB a b ==> (fIN a fs <=> b IN s)
End

Theorem fIN_IN:
  (AB ===> FSET AB ===> (=)) fIN (IN)
Proof
  simp[FUN_REL_def, FSET_def]
QED

Theorem fEMPTY_EMPTY:
  FSET AB FEMPTY EMPTY
Proof
  simp[FSET_def]
QED

Theorem fUNION_UNION:
  (FSET AB ===> FSET AB ===> FSET AB) fUNION (UNION)
Proof
  simp[FUN_REL_def, FSET_def] >> metis_tac[]
QED

Theorem fINSERT_INSERT:
  bi_unique AB ==>
  (AB ===> FSET AB ===> FSET AB) fINSERT (INSERT)
Proof
  simp[FUN_REL_def, FSET_def, bi_unique_def, left_unique_def,
       right_unique_def] >> metis_tac[]
QED

Overload fDELETE = “fdomsub : 'a fset -> 'a -> 'a fset”
Theorem fDELETE_DELETE:
  bi_unique AB ==>
  (FSET AB ===> AB ===> FSET AB) fDELETE (DELETE)
Proof
  simp[FUN_REL_def, FSET_def, bi_unique_def, left_unique_def,
       right_unique_def] >> metis_tac[]
QED

Overload toSet = “FDOM : 'a fset -> 'a set”
Theorem toSet_correct:
  (FSET AB ===> AB ===> (=)) toSet I
Proof
  simp[FUN_REL_def, FSET_def] >> simp[IN_DEF]
QED

Theorem bi_unique_FSET[simp]:
  bi_unique AB ∧ bitotal AB ==> bi_unique (FSET AB)
Proof
  simp[bi_unique_def, FSET_def, left_unique_def, right_unique_def,
       bitotal_def, total_def, surj_def, pred_setTheory.EXTENSION, fmap_EXT] >>
  metis_tac[]
QED

Theorem KT_FINITE:
  surj AB /\ right_unique AB ==> (FSET AB ===> (=)) (K T) FINITE
Proof
  rw[FUN_REL_def, FSET_def, right_unique_def, total_def, surj_def] >>
  fs[SKOLEM_THM] >>
  ‘b = { e | fIN (f e) a }’
    by simp[pred_setTheory.EXTENSION] >>
  qabbrev_tac ‘a0 = { f e | e | fIN (f e) a /\ e IN b }’ >>
  ‘a0 SUBSET FDOM a’ by simp[SUBSET_DEF, Abbr‘a0’, PULL_EXISTS] >>
  ‘FINITE a0’ by metis_tac[SUBSET_FINITE, FDOM_FINITE] >>
  ‘a0 = IMAGE f b’ by simp[Abbr‘a0’, EXTENSION] >>
  ‘!e1 e2. f e1 = f e2 <=> e1 = e2’ by metis_tac[] >>
  metis_tac[INJECTIVE_IMAGE_FINITE]
QED

Theorem total_FSET:
  left_unique AB ==> total (FSET AB)
Proof
  simp[total_def, left_unique_def] >> strip_tac >> qx_gen_tac ‘fs’ >>
  qexists_tac ‘{ b | ?a. AB a b /\ fIN a fs }’ >>
  simp[FSET_def, EXTENSION] >> metis_tac[]
QED

Theorem FORALL_FSET:
  left_unique AB ==>
  ((FSET AB ===> combin$C (==>)) ===> combin$C (==>)) (!) (!)
Proof
  strip_tac >> simp[FUN_REL_def] >>
  qx_genl_tac [‘fsP’, ‘sP’] >>
  ‘fsP = \fs. fsP fs’ by simp[FUN_EQ_THM] >> pop_assum SUBST_ALL_TAC >>
  ‘sP = \s. sP s’ by simp[FUN_EQ_THM] >> pop_assum SUBST_ALL_TAC >> rw[] >>
  ‘total (FSET AB)’ suffices_by metis_tac[total_def] >> simp[total_FSET]
QED

Theorem FSET_EQ:
  bi_unique AB /\ bitotal AB ==>
  (FSET AB ===> FSET AB ===> (=)) (=) (=)
Proof
  strip_tac >> simp[FUN_REL_def] >>
  ‘bi_unique (FSET AB)’ suffices_by
    metis_tac[bi_unique_def, left_unique_def, right_unique_def] >>
  simp[bi_unique_FSET]
QED

val abs1 =
    fUNION_UNION |> REWRITE_RULE [FUN_REL_def]
                 |> SIMP_RULE bool_ss [PULL_FORALL]
                 |> Q.SPECL [‘fs1’, ‘s1’, ‘fs2’, ‘s2’]
                 |> UNDISCH_ALL
val abs2 =
    fUNION_UNION |> REWRITE_RULE [FUN_REL_def]
                 |> SIMP_RULE bool_ss [PULL_FORALL]
                 |> Q.SPECL [‘fs2’, ‘s2’, ‘fs1’, ‘s1’]
                 |> UNDISCH_ALL

val fall' = ONCE_REWRITE_RULE [FUN_REL_def] FORALL_FSET |> UNDISCH_ALL

val AB = “AB : 'a -> 'b -> bool”
val eq =
    FSET_EQ |> REWRITE_RULE [ASSUME “bi_unique ^AB”, ASSUME “bitotal ^AB”]
            |> SIMP_RULE bool_ss [PULL_FORALL, FUN_REL_def]
            |> C MATCH_MP abs1 |> C MATCH_MP abs2
            |> CONV_RULE (FORK_CONV(UNBETA_CONV “fs2:'a |-> unit”,
                                    UNBETA_CONV “s2: 'b -> bool”))
            |> DISCH “FSET AB fs2 s2”
            |> Q.GENL [‘fs2’, ‘s2’]
            |> CONV_RULE (REWR_CONV (GSYM FUN_REL_def))
            |> MATCH_MP (GEN_ALL FUN_REL_IFF_IMP)
            |> CONJUNCT2
            |> MATCH_MP fall'
            |> CONV_RULE (FORK_CONV(UNBETA_CONV “fs1: 'a |-> unit”,
                                    UNBETA_CONV “s1:'b -> bool”))
            |> DISCH “FSET AB fs1 s1”
            |> Q.GENL [‘fs1’, ‘s1’]
            |> CONV_RULE (REWR_CONV (GSYM FUN_REL_def))
            |> MATCH_MP fall'
            |> PROVE_HYP (REWRITE_RULE [bi_unique_def]
                                       (ASSUME “bi_unique ^AB”) |> CONJUNCT1)
            |> INST_TYPE [beta |-> alpha]
            |> INST [“AB:'a -> 'a -> bool” |-> “(=) : 'a -> 'a -> bool”]
            |> PROVE_HYP bi_unique_EQ |> PROVE_HYP bitotal_EQ
            |> REWRITE_RULE [combinTheory.C_THM]
            |> C MATCH_MP UNION_COMM


val _ = export_theory();
