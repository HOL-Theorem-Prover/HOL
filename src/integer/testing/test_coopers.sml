open HolKernel Parse;

val _ = Portable.catch_SIGINT()

val result =
    test_cases.perform_tests Cooper.COOPER_CONV Cooper.COOPER_TAC andalso
    test_cases.perform_cooper_tests Cooper.COOPER_CONV
val _ =
    case CommandLine.arguments() of
      [] => ()
    | _ => Profile.print_profile_results (Profile.results())

val _ = Process.exit (if result then Process.success else Process.failure)

