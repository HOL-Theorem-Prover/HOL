open HolKernel Parse;

prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

val _ = (test_cases.perform_tests Cooper.COOPER_CONV;
         case CommandLine.arguments() of
           [] => ()
         | _ => Profile.print_profile_results (Profile.results()));
