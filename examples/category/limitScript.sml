open HolKernel bossLib boolLib categoryTheory nat_transTheory pairTheory lcsymtacs;

val _ = new_theory "limit";

val is_terminal_def = Define`
  is_terminal c y = y ∈ c.obj ∧ ∀x. x ∈ c.obj ⇒ ∃!f. f :- x → y-:c`;

val is_initial_def = Define`
  is_initial c x = is_terminal (op_cat c) x`;

val is_initial_thm = Q.store_thm(
"is_initial_thm",
`∀c x. is_category c ⇒ (is_initial c x = x ∈ c.obj ∧ ∀y. y ∈ c.obj ⇒ ∃!f. f :- x → y-:c)`,
metis_tac [is_initial_def,is_terminal_def,op_cat_maps_to_in,op_cat_idem,op_cat_obj,op_mor_idem])

val terminal_unique = Q.store_thm(
"terminal_unique",
`∀c x y. is_category c ∧ is_terminal c x ∧ is_terminal c y ⇒ uiso_objs c x y`,
srw_tac [][uiso_objs_thm] >>
simp_tac (srw_ss()) [EXISTS_UNIQUE_THM] >>
reverse conj_tac >- metis_tac [is_terminal_def] >>
`∃f. f :- x → y-:c` by metis_tac [is_terminal_def] >>
qexists_tac `f` >> srw_tac [][iso_def] >>
`∃g. g :- y → x-:c` by metis_tac [is_terminal_def] >>
qexists_tac `g` >> srw_tac [][iso_pair_def]
>- metis_tac [maps_to_composable,FST,SND]
>> PROVE_TAC [is_terminal_def,id_maps_to,maps_to_comp,maps_to_def,maps_to_in_def,mor_obj]);

val initial_unique = Q.store_thm(
"initial_unique",
`∀c x y. is_category c ∧ is_initial c x ∧ is_initial c y ⇒ uiso_objs c x y`,
metis_tac [terminal_unique,is_initial_def,is_category_op_cat,op_cat_uiso_objs]);

val cone_cat = Define`
  cone_cat f = comma_cat (itself_functor f) (diagonal_functor f.dom f.cod)`;

val is_limit_def = Define`
  is_limit d l = is_functor d ∧ is_terminal (cone_cat d) l`;

val _ = export_theory ();
