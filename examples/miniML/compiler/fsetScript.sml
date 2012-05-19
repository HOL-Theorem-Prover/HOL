open HolKernel bossLib boolLib pred_setTheory finite_mapTheory lcsymtacs
val _ = new_theory "fset"

val a_linear_order_def = Define`
  a_linear_order = @r. antisymmetric r ∧ transitive r ∧ total r`

val force_dom_def = Define`
  force_dom fm s d = FUN_FMAP (λx. if x ∈ FDOM fm ∩ s then fm ' x else d) s`

val fresh_var_def = Define`
  fresh_var s = num_to_hex_string (LEAST n. num_to_hex_string n ∉ s)`

val _ = export_theory();
