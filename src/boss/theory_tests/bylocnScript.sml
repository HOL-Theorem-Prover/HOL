open HolKernel Parse boolLib bossLib;

val _ = new_theory "bylocn";

val c = ref 0

fun test l suffp q =
  (c := !c + 1;
   store_thm("test" ^ Int.toString (!c),
     ``something impossible : bool``,
     (if suffp then q suffices_by ALL_TAC
      else q by ALL_TAC))
     handle e as HOL_ERR {message, origin_structure, origin_function, ...} =>
            if suffp then
              if message = "suffices_by's tactic failed to prove goal on line "^
                           Int.toString l
              then save_thm("test" ^ Int.toString (!c), TRUTH)
              else raise e
            else if message = "by's tactic failed to prove subgoal on line "^
                              Int.toString l
            then save_thm("test" ^ Int.toString (!c), TRUTH)
            else raise e)

val _ = test 24 false `foo:bool`;
val _ = test 25 true `foo:bool`;

val _ = test 27 false `^(concl TRUTH)`;
val _ = test 28 true `^(concl TRUTH)`;

val t = concl TRUTH

val _ = test 32 false `^t`;
val _ = test 33 true `^t`;


val _ = export_theory();
