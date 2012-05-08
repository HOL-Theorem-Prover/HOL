open HolKernel bossLib boolLib countableLib lcsymtacs
val _ = new_theory "countable"

val [count_bool_aux_inj_rwt] = mk_count_aux_inj_rwt [``:bool``]
val [count_list_aux_inj_rwt] = mk_count_aux_inj_rwt [``:α list``]

val count_list_aux_cong = store_thm(
"count_list_aux_cong",
``∀l1 l2 f f'. (l1 = l2) ∧ (∀x. MEM x l2 ⇒ (f x = f' x)) ⇒ (count_list_aux f l1 = count_list_aux f' l2)``,
rw[] >> Induct_on `l1` >>
rw[definition "count_list_aux_def"])
val _ = DefnBase.export_cong"count_list_aux_cong"

val [count_option_aux_inj_rwt] = mk_count_aux_inj_rwt [``:α option``]
val [count_prod_aux_inj_rwt] = mk_count_aux_inj_rwt [``:α # β``]

val count_prod_aux_cong = store_thm(
"count_prod_aux_cong",
``∀p1 p2 ca ca' cb cb'. (p1 = p2) ∧ (∀x. (x = FST p2) ⇒ (ca x = ca' x)) ∧ (∀x. (x = SND p2) ⇒ (cb x = cb' x))
    ⇒ (count_prod_aux ca cb p1 = count_prod_aux ca' cb' p2)``,
rw[] >> Cases_on `p1` >> fs[])
val _ = DefnBase.export_cong"count_prod_aux_cong"

val _ = export_theory()
