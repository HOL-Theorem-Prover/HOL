signature Prim_rec_Compat =
sig
  val old_style_to_new : Thm.thm -> Thm.thm
  val prove_constructors_one_one : Thm.thm -> Thm.thm
  val prove_constructors_distinct : Thm.thm -> Thm.thm
  val prove_cases_thm : Thm.thm -> Thm.thm
end;
