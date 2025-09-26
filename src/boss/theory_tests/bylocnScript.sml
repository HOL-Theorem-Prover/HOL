Theory bylocn
Libs testutils

val c = ref 0

fun test l suffp q =  (* NB: tactic error wrapped by store_thm error handling *)
  (c := !c + 1;
   store_thm("test" ^ Int.toString (!c),
     ``something impossible : bool``,
     (if suffp then q suffices_by ALL_TAC
      else q by ALL_TAC))
     handle e as HOL_ERR herr =>
            if suffp then
              if String.isSuffix
                    ("suffices_by's tactic failed to prove goal on line "^ Int.toString l)
                    (message_of herr)
              then save_thm("test" ^ Int.toString (!c), TRUTH)
              else raise e
            else if String.isSuffix
                     ("by's tactic failed to prove subgoal on line "^ Int.toString l)
                     (message_of herr)
            then save_thm("test" ^ Int.toString (!c), TRUTH)
            else raise e)

val _ = in_repl_mode (test 25 false) `foo:bool`;
val _ = in_repl_mode (test 26 true) `foo:bool`;

val _ = in_repl_mode (test 28 false) `^(concl TRUTH)`;
val _ = in_repl_mode (test 29 true) `^(concl TRUTH)`;

val t = concl TRUTH

val _ = in_repl_mode (test 33 false) `^t`;
val _ = in_repl_mode (test 34 true) `^t`;
