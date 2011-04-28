open HolKernel boolLib Parse

open pairTheory optionTheory

val _ = new_theory "state_option"

val _ = type_abbrev("state_option", ``:'a -> ('b # 'a) option``);
val _ = temp_type_abbrev("monad", ``:('a,'b) state_option``);

val STATE_OPTION_FAIL_def = new_definition(
  "STATE_OPTION_FAIL_def",
  ``STATE_OPTION_FAIL : ('a,'b) monad s = NONE``);

val STATE_OPTION_UNIT_def = new_definition(
  "STATE_OPTION_UNIT_def",
  ``STATE_OPTION_UNIT : 'b -> ('a,'b) monad a s = SOME (a,s)``);

val STATE_OPTION_BIND_def = new_definition(
  "STATE_OPTION_BIND_def",
  ``STATE_OPTION_BIND
      (m : ('a,'b)monad)
      (f:'b -> ('a,'c) monad) : ('a,'c) monad
      s
    =
      OPTION_BIND (m s) (UNCURRY f)``);

val STATE_OPTION_IGNORE_BIND_def = new_definition(
  "STATE_OPTION_IGNORE_BIND_def",
  ``STATE_OPTION_IGNORE_BIND
      (m1 : ('a,'b) monad)
      (m2 : ('a,'c) monad) : ('a,'c) monad
      s
    =
      OPTION_BIND (m1 s) (m2 o SND)``);

val STATE_OPTION_LIFT_def = new_definition(
  "STATE_OPTION_LIFT_def",
  ``(STATE_OPTION_LIFT : 'b option -> ('a,'b) monad) m s =
    OPTION_BIND m (\a. SOME (a,s))``);

(* Commands to make the above look nice with monadsyntax in place.
val _ = overload_on("monad_bind", ``STATE_OPTION_BIND o STATE_OPTION_LIFT``);
val _ = overload_on("monad_unitbind", ``STATE_OPTION_IGNORE_BIND o STATE_OPTION_LIFT``);
val _ = overload_on("monad_bind", ``STATE_OPTION_BIND``);
val _ = overload_on("monad_unitbind", ``STATE_OPTION_IGNORE_BIND``);
val _ = overload_on("return", ``STATE_OPTION_UNIT``);
*)

val _ = export_theory ()
