open HolKernel Parse;

prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

val result = test_cases.perform_tests Omega.OMEGA_CONV Omega.OMEGA_TAC
val _ = case CommandLine.arguments() of
          [] => ()
        | _ => Profile.print_profile_results (Profile.results())
val _ = Process.exit (if result then Process.success else Process.failure)


