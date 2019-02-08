open HolKernel Parse boolLib bossLib;
open bagTheory;

val _ = new_theory "unibag";

val _ = overload_on ("unibag", ``\b. BAG_OF_SET (SET_OF_BAG b)``);

val unibag_thm = save_thm("unibag_thm", CONJ BAG_OF_SET SET_OF_BAG);

Theorem unibag_INSERT `!a b. (unibag (BAG_INSERT a b))
= BAG_MERGE {|a|} (unibag b)` (
  rw[BAG_OF_SET_INSERT,SET_OF_BAG_INSERT]);

Theorem unibag_UNION `!a b. unibag (a + b) = BAG_MERGE (unibag a) (unibag b)` (
  rw[SET_OF_BAG_UNION,BAG_OF_SET_UNION]);

Theorem unibag_IN `!e b. BAG_IN e b ==> BAG_IN e (unibag b)` (
  rw[IN_SET_OF_BAG,BAG_IN_BAG_OF_SET]);

Theorem unibag_EQ_BAG_INSERT
        `!e b b'. (unibag b = BAG_INSERT e b') ==> ?c. (b' = unibag c)` (
  rw[] >>
    fs[unibag_thm,BAG_INSERT,FUN_EQ_THM,BAG_IN,BAG_INN] >>
    qexists_tac `b'` >>
    rw[] >>
    first_x_assum (qspec_then `x` mp_tac) >>
    rw[] >>
    Induct_on `b' e` >>
    rw[]);

Theorem unibag_FINITE `!b. FINITE_BAG b = FINITE_BAG (unibag b)`
(rw[] >> EQ_TAC >> metis_tac[FINITE_SET_OF_BAG, FINITE_BAG_OF_SET]);


Theorem unibag_ALL_DISTINCT `!b. BAG_ALL_DISTINCT (unibag b)` (
  rw[BAG_ALL_DISTINCT]);

Theorem unibag_IN `!e b. BAG_IN e b ==> BAG_IN e (unibag b)` (
  rw[BAG_IN]);

Theorem unibag_EL_MERGE_cases `!e b.
((BAG_IN e b) ==> (BAG_MERGE {|e|} (unibag b) = (unibag b)))
 /\ (~(BAG_IN e b) ==> (BAG_MERGE {|e|} (unibag b) = BAG_INSERT e (unibag b)))` (
  rw[]
    >- (`BAG_ALL_DISTINCT (unibag b)` by metis_tac[unibag_ALL_DISTINCT] >>
        `BAG_ALL_DISTINCT {|e|}` by simp[BAG_ALL_DISTINCT_THM] >>
        `BAG_ALL_DISTINCT (BAG_MERGE {|e|} (unibag b))`
          by simp[BAG_ALL_DISTINCT_BAG_MERGE] >>
        qspecl_then [`BAG_MERGE {|e|} (unibag b)`,`unibag b`] mp_tac
          BAG_ALL_DISTINCT_EXTENSION >>
        rw[] >>
        metis_tac[])
    >- (`BAG_ALL_DISTINCT (unibag b)` by metis_tac[unibag_ALL_DISTINCT] >>
        `BAG_ALL_DISTINCT {|e|}` by simp[BAG_ALL_DISTINCT_THM] >>
        `BAG_ALL_DISTINCT (BAG_MERGE {|e|} (unibag b))`
          by simp[BAG_ALL_DISTINCT_BAG_MERGE] >>
        `BAG_ALL_DISTINCT (BAG_INSERT e (unibag b))`
          by simp[BAG_ALL_DISTINCT] >>
        qspecl_then [`BAG_MERGE {|e|} (unibag b)`,`BAG_INSERT e (unibag b)`]
          mp_tac BAG_ALL_DISTINCT_EXTENSION >>
        rw[]));

Theorem unibag_DECOMPOSE `unibag g <> g ==> ?A g0. g = {|A;A|} + g0` (
  simp[unibag_thm] >>
  simp[SimpL ``$==>``,FUN_EQ_THM,PULL_EXISTS] >>
  rw[]
    >- (qexists_tac `x` >>
        qexists_tac `g (| x |-> g x - 2 |)` >>
        fs[BAG_IN,BAG_INN] >>
        simp[FUN_EQ_THM,BAG_UNION,
             BAG_INSERT,EMPTY_BAG,combinTheory.APPLY_UPDATE_THM] >>
        qx_gen_tac `y` >>
        Cases_on `x=y` >>
        rw[])
    >- fs[BAG_IN,BAG_INN]);

Theorem unibag_SUB_BAG `!b. unibag b <= b`
(rw[unibag_thm,SUB_BAG,BAG_IN,BAG_INN]);

val _ = export_theory();

