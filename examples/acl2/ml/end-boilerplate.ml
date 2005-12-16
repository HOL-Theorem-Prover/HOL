
val thl = map (define_and_overload name_alist) (tl(!acl2_list_ref));

val _ = (acl2_simps := (!acl2_simps) @ thl);

val _ =
 map
  (fn (hol,acl2) =>
    set_MLname (acl2 ^ "_acl2_defun") (hol ^ "_acl2_defun"))
  name_alist;

val _ = acl2_name_list := union (!acl2_name_list) name_alist;

val _ = export_acl2_theory();

