
(* handles nested recursion *)
val define_type :
  (Type.hol_type  * (string * Type.hol_type list) list) list ->
  Thm.thm * Thm.thm