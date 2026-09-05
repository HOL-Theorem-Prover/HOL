(* HolRefute by example, 6: narrowing and partial values. *)

Theory refuteExample06
Libs
  Refute

(* NARROWING_TAC runs only symbolic narrowing.  Narrowing refines the parts
   of an input inspected by the conjecture, so reports may contain function
   updates or holes in otherwise irrelevant data. *)

Theorem every_function_agrees_at_zero_and_one:
  (f : num -> num) 0 = f 1
Proof
  NARROWING_TAC >> cheat
QED

Theorem every_list_has_length_other_than_four:
  LENGTH (xs : num list) <> 4
Proof
  NARROWING_TAC >> cheat
QED

Theorem mapping_any_function_leaves_a_list_unchanged:
  MAP (f : num -> num) xs = xs
Proof
  NARROWING_TAC >> cheat
QED

Datatype:
  colour = Red | Green | Blue
End

Definition code_def:
  (code Red = 0) /\
  (code Green = 1) /\
  (code Blue = 2)
End

Theorem no_colour_has_code_two:
  code c <> 2
Proof
  NARROWING_TAC >> cheat
QED
