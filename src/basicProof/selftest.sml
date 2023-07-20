open Parse BasicProvers simpLib testutils

(* tests for diminish applying to constituents that are "built-in" to srw_ss
   from its point of definition *)
val _ = diminish_srw_ss ["COMBIN"]
val _ = shouldfail {checkexn = (fn Conv.UNCHANGED => true | _ => false),
                    printarg = fn _ => "diminish_srw_ss before 'realisation'",
                    printresult = thm_to_string,
                    testfn = SIMP_CONV (quietly srw_ss()) []}
                   “K T (x:'a)”

val _ = shouldfail {checkexn = (fn Conv.UNCHANGED => true | _ => false),
                    printarg = fn _ => "with_simpset_updates removes BETA_CONV",
                    printresult = thm_to_string,
                    testfn = with_simpset_updates
                               (fn ss0 => ss0 -* ["BETA_CONV"])
                               (fn t => SIMP_CONV (srw_ss()) [] t)}
                   “(λx. x /\ p) T”
