(* HolRefute by example, 12: standard-library types. *)

Theory refuteExample12
Ancestors
  integer string words rat finite_map
Libs
  Refute intLib wordsLib

(* The executable backends use the evaluation support loaded for each
   library type. *)

Theorem adding_one_leaves_an_integer_unchanged:
  (i : int) + 1 = i
Proof
  QUICKCHECK_TAC >> cheat
QED

Theorem appending_a_character_leaves_a_string_unchanged:
  (s : string) ++ "a" = s
Proof
  QUICKCHECK_TAC >> cheat
QED

Theorem incrementing_a_word_never_wraps:
  (w : word4) + 1w <> 0w
Proof
  QUICKCHECK_TAC >> cheat
QED

(* The model finder reads a character as a 256-element carrier ordered by
   code, so character literals and the character orders reach it directly. *)

Theorem no_character_precedes_the_letter_a:
  char_le #"a" (c : char)
Proof
  MODEL_REFUTE_TAC >> cheat
QED

(* The model finder has a relational encoding for rationals. *)

Theorem adding_one_leaves_a_rational_unchanged:
  (r : rat) + 1 = r
Proof
  MODEL_REFUTE_TAC >> cheat
QED

(* Finite maps have a QC generator too, registered on demand at whatever
   instance a goal needs; FEMPTY is always a candidate, so no fixed key
   maps to a fixed value in every finite map. *)

Theorem finite_maps_need_not_map_zero_to_zero:
  FLOOKUP (fm : num |-> num) 0 = SOME (0 : num)
Proof
  QUICKCHECK_TAC >> cheat
QED

(* The model finder has its own relational encoding for finite maps as
   well, reached the same way as any other MODEL_REFUTE_TAC goal:
   agreement at one key does not make two finite maps equal. *)

Theorem two_finite_maps_agreeing_at_one_key_need_not_be_equal:
  FLOOKUP (fm : bool |-> bool) T = FLOOKUP (fm' : bool |-> bool) T ==>
  fm = fm'
Proof
  MODEL_REFUTE_TAC >> cheat
QED
