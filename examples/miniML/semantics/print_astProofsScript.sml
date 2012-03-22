open preamble;
open Print_astTheory Print_astTerminationTheory;

val _ = new_theory "print_astProofs"

val stree_to_string_acc = Q.store_thm ("stree_to_string_acc",
`!st s1 s2. stree_to_string st (s1 ++ s2) = stree_to_string st s1 ++ s2`,
induct_on `st` >>
rw [stree_to_string_def]);

val stree_to_string_append = Q.store_thm ("stree_to_string_append",
`!st1 st2 s. 
  stree_to_string (A st1 st2) s = 
  stree_to_string st1 "" ++ stree_to_string st2 "" ++ s`,
induct_on `st1` >>
rw [stree_to_string_def] >>
induct_on `st2` >>
rw [stree_to_string_def] >>
metis_tac [stree_to_string_acc, STRCAT]);

val _ = export_theory ();
