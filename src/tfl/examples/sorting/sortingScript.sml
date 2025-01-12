(*---------------------------------------------------------------------------*
 *                SPECIFICATION OF SORTING                                   *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib listTheory permTheory;

val MEM_APPEND_DISJ = Q.prove
(`!x l1 l2. MEM x (APPEND l1 l2) = MEM x l1 \/ MEM x l2`,
Induct_on `l1` THEN RW_TAC list_ss [APPEND,MEM] THEN PROVE_TAC[]);


val _ = new_theory "sorting";


(*---------------------------------------------------------------------------*
 * The idea of sortedness requires a "permutation" relation for lists, and   *
 * a "chain" predicate that holds just when the relation R holds between     *
 * all adjacent elements of the list.                                        *
 *---------------------------------------------------------------------------*)

val SORTED_def =
 Define
    `(SORTED R  [] = T)
 /\  (SORTED R [x] = T)
 /\  (SORTED R (x::y::rst) = R x y /\ SORTED R (y::rst))`;


val performs_sorting_def =
 Define
    `performs_sorting f R = !l. PERM l (f R l) /\ SORTED R (f R l)`;


(*---------------------------------------------------------------------------*
 *    When consing onto a sorted list yields a sorted list                   *
 *---------------------------------------------------------------------------*)

val SORTED_eq = Q.store_thm("SORTED_eq",
`!R L x. transitive R
         ==> (SORTED R (x::L) = SORTED R L /\ !y. MEM y L ==> R x y)`,
Induct_on `L`
 THEN RW_TAC list_ss [SORTED_def,MEM]
 THEN PROVE_TAC [relationTheory.transitive_def]);


(*---------------------------------------------------------------------------*
 *       When appending sorted lists gives a sorted list.                    *
 *---------------------------------------------------------------------------*)

val SORTED_APPEND = Q.store_thm("SORTED_APPEND",
`!R L1 L2.
     transitive R
 /\  SORTED R L1
 /\  SORTED R L2
 /\ (!x y. MEM x L1 /\ MEM y L2 ==> R x y)
  ==>
    SORTED R (APPEND L1 L2)`,
Induct_on `L1`
 THEN RW_TAC list_ss [MEM]
 THEN `SORTED R L1 /\ !y. MEM y L1 ==> R h y` by PROVE_TAC [SORTED_eq]
 THEN RW_TAC bool_ss [SORTED_eq]
 THEN `MEM y L1 \/ MEM y L2` by PROVE_TAC [MEM_APPEND_DISJ]
 THEN PROVE_TAC []);


val _ = export_theory();
