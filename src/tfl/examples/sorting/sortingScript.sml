(*---------------------------------------------------------------------------*
 *                SPECIFICATION OF SORTING                                   *
 *---------------------------------------------------------------------------*)

structure sortingScript =
struct

open HolKernel basicHol90Lib bossLib;
infix THEN THENL |->;
infix 8 by;

local open permTheory QLib in end;

val _ = new_theory"sorting";

val mem_def        = listXTheory.mem_def;
val transitive_def = TCTheory.transitive_def;

(*---------------------------------------------------------------------------*
 * The idea of sortedness requires a "permutation" relation for lists, and   *
 * a "chain" predicate that holds just when the relation R holds between     *
 * all adjacent elements of the list.                                        *
 *---------------------------------------------------------------------------*)

val sorted_def = 
 Define
    `(sorted R  [] = T) /\
     (sorted R [x] = T) /\   
     (sorted R (CONS x (CONS y rst)) = R x y /\ sorted R (CONS y rst))`;


val performs_sorting_def = 
 Define
    `performs_sorting f R = !l. perm l (f R l) /\ sorted R (f R l)`;


(*---------------------------------------------------------------------------*
 *                    THEOREMS ABOUT SORTEDNESS                              *
 *---------------------------------------------------------------------------*)

val sorted_eqns      = save_thm("sorted_eqns", CONJUNCT1 sorted_def);
val sorted_induction = save_thm("sorted_induction", CONJUNCT2 sorted_def);

(*---------------------------------------------------------------------------*
 *    When consing onto a sorted list yields a sorted list                   *
 *---------------------------------------------------------------------------*)

val sorted_eq = Q.store_thm("sorted_eq",
`!R L x. transitive R
         ==> (sorted R (CONS x L) = sorted R L /\ !y. mem y L ==> R x y)`,
Induct_on `L`
 THEN RW_TAC list_ss [sorted_eqns,mem_def] 
 THEN PROVE_TAC [transitive_def]);


(*---------------------------------------------------------------------------*
 *       When appending sorted lists gives a sorted list.                    *
 *---------------------------------------------------------------------------*)

val sorted_append = Q.store_thm("sorted_append",
`!R L1 L2. 
     transitive R 
 /\  sorted R L1
 /\  sorted R L2
 /\ (!x y. mem x L1 /\ mem y L2 ==> R x y)
  ==> 
    sorted R (APPEND L1 L2)`,
Induct_on `L1`
 THEN RW_TAC list_ss [mem_def] 
 THEN `sorted R L1 /\ !y. mem y L1 ==> R h y` by PROVE_TAC [sorted_eq]
 THEN RW_TAC bool_ss [sorted_eq] 
 THEN `mem y L1 \/ mem y L2` by PROVE_TAC [listXTheory.mem_of_append]
 THEN PROVE_TAC []);


val _ = export_theory();

end;
