
val thl = map (install_and_print o mk_defs) (!acl2_list_ref);

val _ = (acl2_simps := (!acl2_simps) @ thl);

val _ = export_acl2_theory();

