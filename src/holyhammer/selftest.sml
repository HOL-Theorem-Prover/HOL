open testutils

datatype prover = datatype hhProver.prover

(* This quotation is deliberately compiled after hhLamTrans is linked.  A
   compile-time combin-theory dependency used to install its surface grammar
   in HolyHammer sessions (b7fca5c48); this ordinary source fixture must
   retain the ambient grammar. *)
val grammar_pollution_fixture : Term.term = ``(\x : 'a. x) y = y``
val _ =
  (tprint "hhLamTrans does not pollute the term grammar";
   if boolSyntax.is_eq grammar_pollution_fixture then OK ()
   else die "FAILED: hhLamTrans grammar fixture")

fun join a b = OS.Path.concat (a, b)

fun write_file path contents =
  let
    val output = TextIO.openOut path
    val _ = TextIO.output (output, contents)
  in
    TextIO.closeOut output
  end

fun is_dir path = OS.FileSys.isDir path handle OS.SysErr _ => false

val mkdir = hhConfig.ensure_dir
val mkdirs = hhConfig.ensure_dir

fun remove_tree path =
  if is_dir path then
    let
      val stream = OS.FileSys.openDir path
      fun loop () =
        case OS.FileSys.readDir stream of
            NONE => OS.FileSys.closeDir stream
          | SOME name => (remove_tree (join path name); loop ())
      val _ = loop ()
    in
      OS.FileSys.rmDir path
    end
  else OS.FileSys.remove path
  handle OS.SysErr _ => ()

fun make_executable path =
  let
    val _ = write_file path "#!/bin/sh\nexit 0\n"
    val status = OS.Process.system ("/bin/chmod 700 " ^ path)
  in
    if OS.Process.isSuccess status then ()
    else raise Fail ("could not make executable " ^ path)
  end

fun expect message truth =
  (tprint message; if truth then OK () else die ("FAILED: " ^ message))

fun is_some expected actual = actual = SOME expected

fun has_parameter key value source =
  List.exists (fn (key', value', source') =>
    key = key' andalso value = value' andalso source = source')
    (hhConfig.hh_params ())

fun option_error fragments thunk =
  ((thunk (); false)
   handle Feedback.HOL_ERR error =>
     let val message = Feedback.message_of error
     in List.all (fn fragment => String.isSubstring fragment message) fragments
     end
        | _ => false)

fun with_hh_options settings action =
  let
    val previous = List.mapPartial (fn (key, value, source) =>
      if source = "set" andalso
         List.exists (fn (name, _) => key = name) settings
      then SOME (key, value) else NONE) (hhConfig.hh_params ())
    fun restore () =
      (List.app (hhConfig.hh_unset o #1) settings;
       List.app hhConfig.hh_set previous)
    val _ = List.app hhConfig.hh_set settings
  in
    (action () before restore ())
    handle exn => (restore (); raise exn)
  end

fun test_child root =
  let
    val home = join root "home"
    val holdir = join root "holdir"
    val hammer = join (join home ".hol4") "hammer"
    val config = join hammer "config"
    val config_exec = join root "config-exec"
    val env_exec = join root "env-exec"
    val path_dir = join root "path"
    val path_exec = join path_dir "path-exec"
    val platform = hhConfig.platform ()
    val system_provers = join (join (join holdir "src") "holyhammer")
                              "provers"
    val user_provers = join hammer "provers"
    val state_provers = join (hhConfig.state_dir ()) "provers"
    fun install root version =
      let
        val dir = join (join root ("installprover-" ^ version)) platform
        val _ = mkdirs dir
        val file = join dir "install-exec"
      in
        make_executable file; file
      end
    val system_old = install system_provers "1.0"
    val system_new = install system_provers "2.0"
    val user_new = install user_provers "9.0"
    val state_exec =
      let
        val dir = join (join state_provers "stateprover-3.0") platform
        val _ = mkdirs dir
        val file = join dir "state-exec"
      in
        make_executable file; file
      end
    (* Pre-download-provers installations put the binary straight into
       provers/, with no version or platform directory. *)
    val flat_exec =
      let val file = join system_provers "flat-exec" in
        mkdirs system_provers; make_executable file; file
      end
    val _ = make_executable config_exec
    val _ = make_executable env_exec
    val _ = mkdirs path_dir
    val _ = make_executable path_exec
    val config_contents =
      ("# user configuration\n\
       \priority = user # comments are ignored\n\
       \integer = 42\n\
       \enabled = YeS\n\
       \path.value = ~/.fixture\n\
       \plain = key = value\n\
       \timeout = 21\n\
       \cores = 3\n\
       \prover.e.executable = " ^ config_exec ^ "\n")
    val _ = write_file config config_contents
    val _ = expect "state directory" (OS.FileSys.isDir (hhConfig.state_dir ()))
    val _ = expect "comment and assignment parsing"
      (is_some "key = value" (hhConfig.get "plain"))
    val _ = expect "user config overrides system config and environment"
      (is_some "user" (hhConfig.get "priority"))
    val _ = expect "environment key mangling"
      (is_some "environment" (hhConfig.get "mangled.key"))
    val expected_eval =
      case OS.Process.getEnv "HHEVAL_INTEGRATION_TEST" of
          SOME path =>
            (case OS.Process.getEnv "HOL4_HAMMER_EVAL_DIR" of
                 SOME directory => directory
               | NONE => path)
        | NONE => join (join (join holdir "src") "holyhammer") "eval"
    val _ = expect "built-in default"
      (is_some expected_eval (hhConfig.get "eval.dir"))
    val _ = expect "system configuration"
      (is_some "system only" (hhConfig.get "system.only"))
    val _ = expect "integer configuration"
      (hhConfig.get_int "integer" = SOME 42)
    val _ = expect "Boolean configuration"
      (hhConfig.get_bool "enabled" = SOME true)
    val _ = expect "path configuration"
      (is_some (join home ".fixture") (hhConfig.get_path "path.value"))
    val _ = expect "option config overrides option environment"
      (hhConfig.hh_get "timeout" = "21" andalso
       is_some "21" (hhConfig.get "timeout"))
    val _ = hhConfig.hh_set ("timeout", "23")
    val _ = expect "runtime option overrides config"
      (hhConfig.hh_get "timeout" = "23" andalso
       is_some "23" (hhConfig.get "timeout"))
    val _ = expect "unknown option is a descriptive HOL_ERR"
      (option_error ["unknown", "valid keys", "timeout"]
        (fn () => hhConfig.hh_set ("not_an_option", "1")))
    val _ = expect "unparsable option is a descriptive HOL_ERR"
      (option_error ["timeout", "positive integer", "valid keys"]
        (fn () => hhConfig.hh_set ("timeout", "not-an-integer")))
    val _ = expect "failed validation preserves the runtime value"
      (hhConfig.hh_get "timeout" = "23")
    val _ = expect "provers are validated at set time"
      (option_error ["provers", "prover names: e, vampire, zipperposition, z3"]
        (fn () => hhConfig.hh_set
          ("provers", "not-a-holyhammer-prover")))
    val _ = expect "unknown unset option is a HOL_ERR"
      (option_error ["unknown", "valid keys"]
        (fn () => hhConfig.hh_unset "not_an_option"))
    val _ = hhConfig.hh_set ("preplay_timeout", "2.5")
    val _ = hhConfig.hh_set ("minimize_timeout", "3.5")
    val _ = hhConfig.hh_set ("max_facts", "17")
    val _ = List.app
      (fn filter =>
        (hhConfig.hh_set ("filter", filter);
         expect ("filter vocabulary accepts '" ^ filter ^ "'")
           (#filter (hhConfig.snapshot ()) = filter)))
      ["", "knn", "mepo", "mash", "mesh", "none"]
    val _ = expect "filter vocabulary rejects unknown names"
      (option_error ["filter", "knn", "mepo", "mash", "mesh", "none"]
        (fn () => hhConfig.hh_set ("filter", "not-a-filter")))
    val _ = hhConfig.hh_unset "filter"
    val _ = expect "format vocabulary is validated at set time"
      (option_error ["format", "supported TPTP format"]
        (fn () => hhConfig.hh_set ("format", "bad-format")))
    val _ = expect "type encoding vocabulary is validated at set time"
      (option_error ["type_enc", "supported type encoding"]
        (fn () => hhConfig.hh_set ("type_enc", "bad-encoding")))
    val _ = expect "lambda vocabulary is validated at set time"
      (option_error ["lam_trans", "supported lambda translation"]
        (fn () => hhConfig.hh_set ("lam_trans", "bad-lambda")))
    val _ = hhConfig.hh_set ("format", "tf0")
    val _ = hhConfig.hh_set ("type_enc", "mono_native")
    val _ = hhConfig.hh_set ("lam_trans", "lifting")
    val _ = hhConfig.hh_set ("mono_iters", "4")
    val _ = hhConfig.hh_set ("mono_instances", "77")
    val _ = hhConfig.hh_set ("minimize", "off")
    val _ = hhConfig.hh_set ("cache", "yes")
    val _ = hhConfig.hh_set ("debug_dir", join root "debug")
    val quiet = not (#verbose (hhConfig.snapshot ()))
    val drop_one = #preplay_drop_one (hhConfig.snapshot ())
    val _ = hhConfig.hh_set ("verbose", "on")
    val _ = hhConfig.hh_set ("preplay_drop_one", "off")
    val options : hhConfig.hh_options = hhConfig.snapshot ()
    val _ = expect "verbose is off by default and parsed as a Boolean"
      (quiet andalso #verbose options)
    val _ = expect "preplay_drop_one is on by default and parsed as a Boolean"
      (drop_one andalso not (#preplay_drop_one options))
    val _ = expect "snapshot parses values and computes slices"
      (#timeout options = 23 andalso #max_proofs options = 4 andalso
       #provers options = [Eprover, Vampire, Zipperposition] andalso
       #cores options = 3 andalso #slices options = 72 andalso
       #filter options = "none" andalso #max_facts options = SOME 17 andalso
       #format options = "tf0" andalso #type_enc options = "mono_native" andalso
       #lam_trans options = "lifting" andalso #mono_iters options = 4 andalso
       #mono_instances options = SOME 77 andalso not (#minimize options) andalso
       #cache options andalso
       #cache_dir options = join (hhConfig.state_dir ()) "cache" andalso
       #cache_max_entries options = 100000 andalso
       #debug_dir options = SOME (join root "debug"))
    val _ = expect "snapshot parses reconstruction timeouts"
      (Real.abs (#preplay_timeout options - 2.5) < 0.000001
       andalso
       Real.abs (#minimize_timeout options - 3.5) < 0.000001)
    val _ = expect "hh_params reports all four provenance layers"
      (has_parameter "timeout" "23" "set" andalso
       has_parameter "cores" "3" "config" andalso
       has_parameter "filter" "none" "env" andalso
       has_parameter "format" "tf0" "set" andalso
       has_parameter "type_enc" "mono_native" "set" andalso
       has_parameter "lam_trans" "lifting" "set" andalso
       has_parameter "mono_iters" "4" "set" andalso
       has_parameter "mono_instances" "77" "set" andalso
       has_parameter "max_proofs" "4" "default")
    val _ = hhConfig.print_params ()
    val _ = holyHammer.set_timeout 19
    val _ = expect "set_timeout updates the runtime option"
      (hhConfig.hh_get "timeout" = "19")
    val _ = hhConfig.hh_unset "timeout"
    val _ = expect "hh_unset restores config precedence"
      (hhConfig.hh_get "timeout" = "21")
    val _ = write_file config
      ("provers = not-a-holyhammer-prover\n" ^ config_contents)
    val _ = expect "provers are validated at snapshot time"
      (option_error ["provers", "prover names: e, vampire"]
        (fn () => ignore (hhConfig.snapshot ())))
    val _ = write_file config config_contents
    val _ = hhConfig.hh_set ("provers", "e vampire")
    val _ = expect "prover lists parse to provers"
      (#provers (hhConfig.snapshot ()) = [Eprover, Vampire])
    val _ = hhConfig.hh_unset "provers"
    val _ = List.app hhConfig.hh_unset
      ["format", "type_enc", "lam_trans", "mono_iters", "mono_instances",
       "verbose", "preplay_drop_one"]
    val default_options : hhConfig.hh_options = hhConfig.snapshot ()
    val _ = expect "new option defaults preserve per-slice values"
      (#filter default_options = "none" andalso
       #format default_options = "" andalso
       #type_enc default_options = "" andalso
       #lam_trans default_options = "" andalso
       #mono_iters default_options = 3 andalso
       #mono_instances default_options = NONE andalso
       hhConfig.hh_get "mono_instances" = "")
    fun workers_with settings =
      #export_workers (hhConfig.snapshot_with (("cores", "3") :: settings))
    val _ = expect "export_workers: two by default, 1 means inline, 0 means \
      \cores, capped by cores"
      (#export_workers default_options =
         Int.min (2, #cores default_options) andalso
       workers_with [] = 2 andalso
       workers_with [("export_workers", "1")] = 1 andalso
       workers_with [("export_workers", "0")] = 3 andalso
       workers_with [("export_workers", "2")] = 2 andalso
       workers_with [("export_workers", "16")] = 3)
    val overridden = hhConfig.snapshot_with
      [("max_proofs", "2"), ("mono_instances", "9"), ("debug_dir", "")]
    val _ = expect "snapshot overrides leave the runtime settings alone"
      (#max_proofs overridden = 2 andalso
       #mono_instances overridden = SOME 9 andalso
       #debug_dir overridden = NONE andalso
       hhConfig.hh_get "mono_instances" = "")
    val _ = expect "invalid and unknown snapshot overrides are rejected"
      (((hhConfig.snapshot_with [("max_proofs", "x")]; false)
          handle Feedback.HOL_ERR _ => true) andalso
       ((hhConfig.snapshot_with [("no_such_option", "1")]; false)
          handle Feedback.HOL_ERR _ => true))
    fun find_test_exec prover = hhConfig.find_exec prover "HOL4_UNSET_EXEC"
    val find_e_exec = hhConfig.find_exec "e" "HOL4_EPROVER_EXECUTABLE"
    val _ = expect "configuration executable discovery"
      (is_some config_exec (find_e_exec ["path-exec"]))
    val _ = write_file config
      ("priority = user # comments are ignored\n\
       \integer = 42\n\
       \enabled = YeS\n\
       \path.value = ~/.fixture\n\
       \plain = key = value\n\
       \eval.dir = config-eval\n")
    val _ = expect "configuration overrides the built-in default"
      (is_some "config-eval" (hhConfig.get "eval.dir"))
    val _ = expect "environment is effective after config removal"
      (hhConfig.hh_get "timeout" = "22" andalso
       has_parameter "timeout" "22" "env")
    val _ = expect "prover environment executable discovery"
      (is_some env_exec (find_e_exec ["path-exec"]))
    val _ = expect "PATH executable discovery"
      (is_some path_exec (find_test_exec "pathprover" ["path-exec"]))
    val _ = expect "state-directory installation discovery"
      (is_some state_exec
       (find_test_exec "stateprover" ["state-exec"]))
    val _ = expect "newest system installation is preferred"
      (is_some system_new
       (find_test_exec "installprover" ["install-exec"]))
    val _ = expect "install search precedes user installation"
      (find_test_exec "installprover" ["install-exec"] <> SOME user_new)
    val _ = expect "older installation is not selected"
      (find_test_exec "installprover" ["install-exec"] <> SOME system_old)
    val _ = expect "legacy flat installation discovery"
      (is_some flat_exec (find_test_exec "flatprover" ["flat-exec"]))
    val _ = expect "versioned installation precedes the legacy layout"
      (is_some system_new
       (find_test_exec "installprover" ["install-exec"]))
    val _ = expect "dump reports provenance"
      (List.exists (fn (key, value) =>
         key = "priority" andalso String.isPrefix "config: " value)
       (hhConfig.dump ()))
  in
    ()
  end

fun make_fixture root =
  let
    val home = join root "home"
    val holdir = join root "holdir"
    val hammer = join (join home ".hol4") "hammer"
    val _ = mkdirs hammer
    val _ = mkdirs (join holdir "etc")
    val _ = write_file (join (join holdir "etc") "hammer-config")
      "priority = system\nplain = system value\nsystem.only = system only\n"
  in
    (home, holdir, join root "path", join root "env-exec")
  end

fun run_parent () =
  let
    val root = OS.FileSys.tmpName ()
    val _ = OS.FileSys.remove root handle OS.SysErr _ => ()
    val _ = OS.FileSys.mkDir root
    val (home, holdir, path, env_exec) = make_fixture root
    (* the children must not see the caller's prover installations *)
    val clean_env =
      "/usr/bin/env -u HOL4_VAMPIRE_EXECUTABLE" ^
      " -u HOL4_ZIPPERPOSITION_EXECUTABLE -u HOL4_Z3_EXECUTABLE"
    val command =
      clean_env ^ " HOL4_HAMMER_PRIORITY=environment" ^
      " HOL4_HAMMER_MANGLED_KEY=environment" ^
      " HOL4_HAMMER_TIMEOUT=22" ^
      " HOL4_HAMMER_FILTER=none" ^
      " HOL4_EPROVER_EXECUTABLE=" ^ env_exec ^
      " HOL4_HAMMER_DIR=" ^ join root "state" ^
      " HHCONFIG_TEST_ROOT=" ^ root ^
      " HOLDIR=" ^ holdir ^
      " PATH=" ^ path ^
      " ./selftest.exe"
    val env_command =
      clean_env ^ " -u HOL4_EPROVER_EXECUTABLE" ^
      " HOL4_HAMMER_EVAL_DIR=environment-eval" ^
      " HHCONFIG_ENV_DEFAULT_TEST=environment-eval" ^
      " HHCONFIG_TEST_ROOT=" ^ root ^
      " HOLDIR=" ^ holdir ^
      " PATH=" ^ path ^
      " ./selftest.exe"
    val _ = tprint "hhConfig hermetic selftests"
    val first = OS.Process.system command
    val _ = write_file (join (join (join home ".hol4") "hammer")
                            "config") "# no eval.dir here\n"
    val second = OS.Process.system env_command
    val _ = remove_tree root
  in
    if OS.Process.isSuccess first andalso OS.Process.isSuccess second then OK ()
    else die "FAILED: hhConfig child selftest"
  end

fun test_environment_default value =
  let
    val options : hhConfig.hh_options = hhConfig.snapshot ()
    val _ = expect "environment overrides the built-in default"
      (is_some value (hhConfig.get "eval.dir"))
    val _ = expect "effective timeout default is 30"
      (#timeout options = 30 andalso hhConfig.hh_get "timeout" = "30" andalso
       has_parameter "timeout" "30" "default")
    val _ = expect "default cores and slices are computed"
      (#cores options > 0 andalso #slices options = 24 * #cores options)
    val _ = expect "empty option defaults map to NONE"
      (#max_facts options = NONE andalso #debug_dir options = NONE)
    val _ = expect "empty filter default keeps per-slice filters"
      (#filter options = "")
  in
    ()
  end

val _ =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      NONE => run_parent ()
    | SOME root =>
      (case OS.Process.getEnv "HHCONFIG_ENV_DEFAULT_TEST" of
           SOME value => test_environment_default value
         | NONE => test_child root)

fun read_lines path =
  let
    val input = TextIO.openIn path
    fun loop lines =
      case TextIO.inputLine input of
          NONE => List.rev lines
        | SOME line => loop (line :: lines)
    val lines = loop []
    val _ = TextIO.closeIn input
  in
    lines
  end

fun expect_equal message expected actual =
  expect message (expected = actual)

fun test_hhTptpProblem () =
  let
    open hhTptpProblem
    val ind = TyCon ("$i", [])
    val bool = TyCon ("$o", [])
    val x = Tm (("X", []), [])
    val a = Tm (("a", []), [])
    val f_x_a = Tm (("f", []), [x, a])
    val predicate =
      Quant (true, [("X", SOME ind)],
        Atom (Tm (("p", []), [f_x_a])))
    val fof : problem =
      [("Facts", [FormLine ("fact", Axiom, predicate)]),
       ("Conjecture", [FormLine ("conjecture", Conjecture,
         Atom (Tm (("p", []), [a])))])]
    val decls =
      [TypeDecl ("ty.i", "i", 0),
       SymDecl ("sy.f", "f", TyFun (ind, TyFun (ind, ind))),
       SymDecl ("sy.p", "p", TyFun (ind, bool))]
    fun typed formula : problem =
      [("Declarations", decls),
       ("Facts", [FormLine ("fact", Axiom, formula)]),
       ("Conjecture", [FormLine ("conjecture", Conjecture,
         Atom (Tm (("p", []), [a])))])]
    val tf0 = TFF {poly = false, fool = NoFool}
    val tx0 = TFF {poly = false,
                   fool = Fool {with_ite = true, with_let = true}}
    val tf1 = TFF {poly = true, fool = NoFool}
    val th0 = THF {poly = false,
                   syntax = {with_ite = false, with_let = false},
                   choice = false}
    val th1 = THF {poly = true,
                   syntax = {with_ite = true, with_let = false},
                   choice = false}
    val ite = Tm (("$ite", []),
      [Tm (("c", []), [x]), f_x_a, a])
    val tx0_formula =
      Quant (true, [("X", SOME ind)], Atom (Tm (("p", []), [ite])))
    val tf1_formula =
      TyQuant (true, ["A"],
        Quant (true, [("X", SOME (TyVar "A"))],
          Atom (Tm (("p", [TyVar "A"]), [x]))))
    val th0_formula =
      Atom (Tm (("p", []), [TmAbs (("Y", ind), Tm (("f", []), [x, a]))]))
    val th1_formula =
      TyQuant (true, ["A"],
        Atom (Tm (("p", [TyVar "A"]), [ite])))
    fun golden name format problem =
      expect_equal ("TPTP golden " ^ name)
        (String.concat (read_lines (join "test-data/problems" name)))
        (string_of_problem format ("hhTptpProblem " ^ name) problem)
    fun fails_with fragment thunk =
      (thunk (); false) handle Fail message =>
        String.isSubstring fragment message
    fun raises thunk = fails_with "" thunk
    val _ = golden "fof.p" FOF fof
    val _ = golden "tf0.p" tf0 (typed predicate)
    val _ = golden "tx0.p" tx0 (typed tx0_formula)
    val _ = golden "tf1.p" tf1 (typed tf1_formula)
    val _ = golden "th0.p" th0 (typed th0_formula)
    val _ = golden "th1.p" th1 (typed th1_formula)
    val uncurry_expected = String.concat
      ["% uncurry\n", "% Declarations (1)\n", "tff(sy.f, type,\n",
       "    f : ($i * $i) > $i).\n"]
    val _ = expect_equal "TFF types are uncurried" uncurry_expected
      (string_of_problem tf0 "uncurry"
        [("Declarations", [SymDecl ("sy.f", "f",
          TyFun (ind, TyFun (ind, ind)))])])
    val _ = expect_equal "type arguments precede TFF term arguments"
      "% args\n%  (1)\ntff(fact, axiom,\n    (f($i,X))).\n"
      (string_of_problem tf0 "args"
        [("", [FormLine ("fact", Axiom,
          Atom (Tm (("f", [ind]), [x])))])])
    val _ = expect_equal "type arguments precede THF term arguments"
      "% args\n%  (1)\nthf(fact, axiom,\n    ((f @ ($i) @ X))).\n"
      (string_of_problem th0 "args"
        [("", [FormLine ("fact", Axiom,
          Atom (Tm (("f", [ind]), [x])))])])
    val _ = expect "$ite prints when enabled"
      (String.isSubstring "$ite(c(X),f(X,a),a)"
        (string_of_problem tx0 "ite"
          [("Facts", [FormLine ("fact", Axiom, Atom ite)])]))
    val _ = expect "$ite rejects disabled syntax"
      (raises (fn () => string_of_problem tf0 "ite"
        [("Facts", [FormLine ("fact", Axiom, Atom ite)])]))
    val let_term = Tm (("$let", []),
      [a, TmAbs (("Y", ind), Tm (("f", []), [x, a]))])
    val _ = expect "$let prints when enabled"
      (String.isSubstring "$let(Y : $i, Y := a, f(X,a))"
        (string_of_problem tx0 "let"
          [("Facts", [FormLine ("fact", Axiom, Atom let_term)])]))
    val _ = expect "$let rejects disabled syntax"
      (raises (fn () => string_of_problem th1 "let"
        [("Facts", [FormLine ("fact", Axiom, Atom let_term)])]))
    val choice = Tm (("@+", []), [TmAbs (("Y", ind), x)])
    val _ = expect "choice printing is rejected"
      (raises (fn () => string_of_problem th0 "choice"
        [("Facts", [FormLine ("fact", Axiom, Atom choice)])]))
    val nested_decls =
      [SymDecl ("s", "s",
         TyPi (["A", "B"],
           TyFun (TyFun (TyVar "A", bool),
             TyCon ("list", [TyVar "B",
               TyCon ("*", [ind, TyFun (ind, ind)])])))),
       SymDecl ("u", "u",
         TyFun (TyFun (ind, bool),
           TyFun (ind, TyCon ("m", [TyFun (ind, ind), ind]))))]
    val _ = expect_equal "nested types print in TFF"
      (String.concat
        ["% n\n%  (2)\ntff(s, type,\n    s : !>[A : $tType, B : $tType]: ",
         "((A > $o) > list(B,($i * ($i > $i))))).\ntff(u, type,\n    ",
         "u : ($i > $o) > $i > m(($i > $i),$i)).\n"])
      (string_of_problem tf1 "n" [("", nested_decls)])
    val _ = expect_equal "nested types print in THF"
      (String.concat
        ["% n\n%  (2)\nthf(s, type,\n    s : !>[A : $tType, B : $tType]: ",
         "((A > $o) > (list @ B @ ($i * ($i > $i))))).\nthf(u, type,\n    ",
         "u : ($i > $o) > $i > (m @ ($i > $i) @ $i)).\n"])
      (string_of_problem th1 "n" [("", nested_decls)])
    val bad_ite = Tm (("$ite", []), [a])
    val _ = expect "the first invalid term in a formula is reported"
      (fails_with "$ite needs exactly three"
        (fn () => string_of_problem tx0 "order"
          [("", [FormLine ("f", Axiom,
            Conn (And, [Atom x, Atom bad_ite, Atom choice]))])]))
    val _ = expect "a disabled $ite precedes a failing child"
      (fails_with "$ite is not enabled"
        (fn () => string_of_problem tf0 "order"
          [("", [FormLine ("f", Axiom,
            Atom (Tm (("$ite", []), [choice, a, a])))])]))
    val _ = expect "an $ite arity error precedes a failing child"
      (fails_with "$ite needs exactly three"
        (fn () => string_of_problem tx0 "order"
          [("", [FormLine ("f", Axiom,
            Atom (Tm (("$ite", []), [choice])))])]))
    val _ = expect "an operand count error precedes a failing child"
      (fails_with "wrong number of operands"
        (fn () => string_of_problem tf0 "order"
          [("", [FormLine ("f", Axiom,
            Conn (Not, [Atom choice, Atom x]))])]))
    val _ = expect "a disabled $let precedes a later choice"
      (fails_with "$let is not enabled"
        (fn () => string_of_problem tf0 "order"
          [("", [FormLine ("f", Axiom,
            Conn (And, [Atom let_term, Atom choice]))])]))
    val _ = expect "the first invalid line of a problem is reported"
      (fails_with "choice is not supported"
        (fn () => string_of_problem th0 "order"
          [("A", [FormLine ("f", Axiom, Atom choice)]),
           ("B", [FormLine ("g", Axiom, Atom let_term)])]))
    val sections = string_of_problem FOF "sections"
      [("First", [FormLine ("one", Axiom, Atom a)]),
       ("Second", [FormLine ("two", Hypothesis, Atom x),
                   FormLine ("three", Conjecture, Atom a)])]
    val _ = expect "sections preserve order and print counts"
      (String.isSubstring "% First (1)\nfof(one" sections andalso
       String.isSubstring "% Second (2)\nfof(two" sections andalso
       String.isSubstring "fof(three" sections andalso
       String.isSubstring "% First (1)" sections andalso
       String.isSubstring "% Second (2)" sections)
  in
    ()
  end

val _ = test_hhTptpProblem ()

fun test_hhTypeEnc () =
  let
    open hhTptpProblem hhTypeEnc
    fun raises fragment thunk =
      (thunk (); false)
      handle Fail message => String.isSubstring fragment message
           | _ => false
    val encodings =
      ["mono_native", "mono_native_fool", "mono_native_higher",
       "mono_native_higher_fool", "poly_native", "mono_guards",
       "mono_guards??", ""]
    val rejected = ["native", "mono_guards?", "poly_guards", " ",
                    "mono_native??"]
    val fof = FOF
    val tf0 = TFF {poly = false, fool = NoFool}
    val tx0 = TFF {poly = false,
                   fool = Fool {with_ite = true, with_let = true}}
    val tf1 = TFF {poly = true, fool = NoFool}
    val th0 = THF {poly = false,
                   syntax = {with_ite = false, with_let = false},
                   choice = false}
    val th1 = THF {poly = true,
                   syntax = {with_ite = true, with_let = false},
                   choice = false}
    fun adjusted format encoding =
      to_string (adjust_type_enc format (of_string encoding))
    fun matrix format expected =
      ListPair.allEq (fn (encoding, result) =>
        case result of
            SOME expected => adjusted format encoding = expected
          | NONE => raises "valid only" (fn () =>
              ignore (adjust_type_enc format (of_string encoding))))
        (encodings, expected)
    val mono = "mono_native"
    val mono_fool = "mono_native_fool"
    val _ = expect "type-encoding grammar round-trips"
      (List.all (fn encoding => to_string (of_string encoding) = encoding)
       encodings)
    val _ = expect "type-encoding grammar rejects all other strings"
      (List.all (fn encoding => raises "unknown type encoding" (fn () =>
         ignore (of_string encoding))) rejected)
    val _ = expect "type encoding adjustment matrix: FOF"
      (matrix fof [SOME "mono_guards", SOME "mono_guards",
                   SOME "mono_guards", SOME "mono_guards",
                   SOME "mono_guards", SOME "mono_guards",
                   SOME "mono_guards??", SOME ""])
    val _ = expect "type encoding adjustment matrix: TF0"
      (matrix tf0 [SOME mono, SOME mono, SOME mono, SOME mono,
                   SOME mono, NONE, NONE, NONE])
    val _ = expect "type encoding adjustment matrix: TX0"
      (matrix tx0 [SOME mono, SOME mono_fool, SOME mono, SOME mono_fool,
                   SOME mono, NONE, NONE, NONE])
    val _ = expect "type encoding adjustment matrix: TF1"
      (matrix tf1 [SOME mono, SOME mono, SOME mono, SOME mono,
                   SOME "poly_native", NONE, NONE, NONE])
    val _ = expect "type encoding adjustment matrix: TH0"
      (matrix th0 [SOME mono, SOME mono, SOME "mono_native_higher",
                   SOME "mono_native_higher", SOME mono, NONE, NONE,
                   NONE])
    val _ = expect "type encoding adjustment matrix: TH1"
      (matrix th1 [SOME mono, SOME mono_fool, SOME "mono_native_higher",
                   SOME "mono_native_higher_fool", SOME "poly_native",
                   NONE, NONE, NONE])
    val _ = bossLib.Hol_datatype
      `hh_typeenc_enum = HHRed | HHBlue | HHGreen`
    val _ = bossLib.Hol_datatype
      `hh_typeenc_recursive = HHStop | HHNext of hh_typeenc_recursive`
    val num_ty = Term.type_of ``0 : num``
    val list_num_ty = Term.type_of ``[] : num list``
    val list_var_ty = Term.type_of ``[] : 'a list``
    val one_ty = Type.mk_type ("one", [])
    val enum_ty = Type.mk_type ("hh_typeenc_enum", [])
    val rec_ty = Type.mk_type ("hh_typeenc_recursive", [])
    val bool_fun_ty = Type.mk_type ("fun", [Type.bool, Type.bool])
    val bool_bool_fun_ty = Type.mk_type ("fun", [Type.bool, bool_fun_ty])
    val num_bool_fun_ty = Type.mk_type ("fun", [num_ty, Type.bool])
    val _ = expect "infinity oracle recognises hardwired types"
      (surely_infinite num_ty)
    val _ = expect "infinity oracle recognises recursive list instances"
      (surely_infinite list_num_ty andalso surely_infinite list_var_ty)
    val _ = expect "infinity oracle keeps finite functions finite"
      (not (surely_infinite bool_fun_ty) andalso
       not (surely_infinite bool_bool_fun_ty))
    val _ = expect "infinity oracle composes infinite function domains"
      (surely_infinite num_bool_fun_ty)
    val _ = expect "infinity oracle treats unknown finite types conservatively"
      (not (surely_infinite Type.bool) andalso not (surely_infinite one_ty)
       andalso not (surely_infinite enum_ty))
    val _ = expect "infinity oracle detects recursive datatypes"
      (surely_infinite rec_ty)
    fun same_types expected actual = expected = actual
    val x = Term.mk_var ("X", one_ty)
    val n = Term.mk_var ("N", num_ty)
    val p = Term.mk_var ("P", Type.mk_type ("fun", [one_ty, Type.bool]))
    val fequal = Term.mk_var ("fequal",
      Type.mk_type ("fun", [one_ty,
        Type.mk_type ("fun", [one_ty, Type.bool])]))
    val naked = boolSyntax.mk_forall (x, boolSyntax.mk_eq (x, x))
    val guarded = boolSyntax.mk_forall (x, Term.mk_comb (p, x))
    val negative = boolSyntax.mk_forall (x,
      boolSyntax.mk_neg (boolSyntax.mk_eq (x, x)))
    val fequal_formula = boolSyntax.mk_forall (x,
      Term.list_mk_comb (fequal, [x, x]))
    val infinite_naked = boolSyntax.mk_forall (n, boolSyntax.mk_eq (n, n))
    val _ = expect "monotonicity calculus finds naked variables"
      (same_types [Type.bool, one_ty] (types_needing_encoding [naked]))
    val _ = expect
      "monotonicity calculus ignores guarded and negative variables"
      (same_types [Type.bool]
        (types_needing_encoding [guarded, negative, infinite_naked]))
    val _ = expect "monotonicity calculus finds fequal variables"
      (same_types [Type.bool, one_ty]
        (types_needing_encoding [fequal_formula]))
  in
    ()
  end

val _ = Feedback.quiet_messages Theory.new_theory "hhStatureTest"

val _ = test_hhTypeEnc ()

fun test_hhLamTrans () =
  let
    open boolSyntax
    val num = Term.type_of ``0 : num``
    val unary = Type.mk_type ("fun", [num, num])
    val binary = Type.mk_type ("fun", [num, unary])
    val x = Term.mk_var ("X", num)
    val y = Term.mk_var ("Y", num)
    val f = Term.mk_var ("F", binary)
    val g = Term.mk_var ("G", unary)
    val h = Term.mk_var ("H", unary)
    val nested_lam = Term.list_mk_abs ([x, y],
      Term.list_mk_comb (f, [Term.mk_comb (g, x), y]))
    val nested = mk_eq (Term.list_mk_comb (nested_lam, [x, y]),
      Term.list_mk_comb (f, [Term.mk_comb (g, x), y]))
    val under_quantifier = mk_forall (h,
      mk_eq (Term.mk_comb (Term.mk_abs (x, Term.mk_comb (h, x)), x),
        Term.mk_comb (h, x)))
    val alpha = Type.mk_vartype "'a"
    val poly_predicate = Type.mk_type ("fun", [alpha, Type.bool])
    val poly_x = Term.mk_var ("PX", alpha)
    val poly_p = Term.mk_var ("PP", poly_predicate)
    val polymorphic_lam =
      Term.mk_abs (poly_x, Term.mk_comb (poly_p, poly_x))
    val polymorphic = mk_eq (Term.mk_comb (polymorphic_lam, poly_x),
      Term.mk_comb (poly_p, poly_x))
    val bool_consumer = Term.mk_var ("BC", Type.mk_type
      ("fun", [Type.bool, Type.bool]))
    val quantified_argument = Term.mk_comb (bool_consumer,
      mk_forall (poly_x, Term.mk_comb (poly_p, poly_x)))
    val t = Term.mk_var ("T0", Type.bool)
    val t1 = Term.mk_var ("T1", Type.bool)
    val t2 = Term.mk_var ("T2", Type.bool)
    val implication_lam = Term.mk_abs (t,
      mk_imp (mk_imp (t1, t), mk_imp (mk_imp (t2, t), t)))
    val function_consumer = Term.mk_var ("FC", Type.mk_type
      ("fun", [Term.type_of implication_lam, Type.bool]))
    val implication_argument =
      Term.mk_comb (function_consumer, implication_lam)
    val nested_quantifier_lam = Term.mk_abs (x,
      mk_forall (y, mk_imp (mk_conj
        (mk_eq (x, x), mk_eq (y, y)), mk_eq (x, y))))
    val nested_function_consumer = Term.mk_var ("NFC", Type.mk_type
      ("fun", [Term.type_of nested_quantifier_lam, Type.bool]))
    val nested_quantifier_argument =
      Term.mk_comb (nested_function_consumer, nested_quantifier_lam)
    val beta_fixtures = [nested, under_quantifier, polymorphic]
    val fixtures =
      beta_fixtures @
      [quantified_argument, implication_argument, nested_quantifier_argument]
    fun formula_abs tm =
      if is_forall tm then formula_abs (#2 (dest_forall tm))
      else if is_exists tm then formula_abs (#2 (dest_exists tm))
      else if is_neg tm then formula_abs (dest_neg tm)
      else if is_conj tm orelse is_disj tm orelse is_imp_only tm then
        formula_abs (lhand tm) orelse formula_abs (rand tm)
      else if is_eq tm andalso Term.type_of (lhand tm) = Type.bool then
        formula_abs (lhand tm) orelse formula_abs (rand tm)
      else term_abs tm
    and term_abs tm =
      if Term.is_abs tm then true
      else if Term.is_comb tm then
        term_abs (Term.rator tm) orelse term_abs (Term.rand tm)
      else false
    fun generated_symbol tm =
      List.all (fn variable =>
        String.isPrefix "lam." (#1 (Term.dest_var variable)))
        (Term.free_vars_lr tm)
    fun normalise tm =
      (rhs (Thm.concl (simpLib.SIMP_CONV boolSimps.bool_ss
        [DB.fetch "combin" "I_THM", DB.fetch "combin" "K_THM",
         DB.fetch "combin" "S_THM", DB.fetch "combin" "C_THM",
         DB.fetch "combin" "o_THM"] tm)) handle UNCHANGED => tm)
    fun has_name stem definitions =
      List.exists (fn (name, _) => name = stem) definitions
    val (lifted, lift_defs) = hhLamTrans.translate hhLamTrans.Lifting fixtures
    val (combs, comb_defs) = hhLamTrans.translate hhLamTrans.Combs fixtures
    val (both, both_defs) =
      hhLamTrans.translate hhLamTrans.CombsAndLifting fixtures
    val (kept, kept_defs) = hhLamTrans.translate hhLamTrans.KeepLams fixtures
    val _ = expect "lambda lifting has deterministic names"
      (map #1 lift_defs = List.tabulate (length lift_defs,
       fn index => "lam." ^ Int.toString index))
    val _ = expect "lifting removes fixture abstractions"
      (List.all (not o formula_abs) lifted andalso
       List.all (fn (_, definition) =>
         not (formula_abs definition)) lift_defs)
    val _ = expect "lifting definitions bind their captured variables"
      (List.all (generated_symbol o #2) lift_defs andalso
       List.exists (fn (_, definition) =>
         List.exists (fn ty => ty = alpha) (Term.type_vars_in_term definition))
         lift_defs)
    val hidden_fixture = ``(\x:num. !y:'b. y = y) = (\x. T)``
    val (_, hidden_defs) =
      hhLamTrans.translate hhLamTrans.Lifting [hidden_fixture]
    fun lambda_symbol definition =
      #1 (strip_comb (lhs (#2 (strip_forall definition))))
    val _ = expect "lifting keeps body-only type variables in symbol types"
      (List.exists (fn (_, definition) =>
         List.exists (fn ty => ty = Type.beta)
           (Type.type_vars (Term.type_of (lambda_symbol definition))))
         hidden_defs andalso
       length (#2 (hhLamTrans.translate hhLamTrans.CombsAndLifting
         [hidden_fixture])) = 2 * length hidden_defs)
    val _ = expect "combs removes fixture abstractions"
      (null comb_defs andalso List.all (not o formula_abs) combs)
    val _ = expect "combs beta-normalise to the closed input"
      (ListPair.allEq (fn (actual, fixture) =>
         Term.aconv (normalise actual)
           (normalise (list_mk_forall (Term.free_vars_lr fixture, fixture))))
       (List.take (combs, length beta_fixtures), beta_fixtures))
    val _ = expect "combs_and_lifting retains both definition forms"
      (ListPair.allEq (fn (left, right) => Term.aconv left right)
         (both, lifted) andalso
       length both_defs = 2 * length lift_defs andalso
       List.all (fn (name, _) =>
         has_name (name ^ ".combs") both_defs) lift_defs andalso
       List.all (not o formula_abs o #2) both_defs)
    val _ = expect "keep_lams only eta-contracts"
      (null kept_defs andalso List.exists formula_abs kept andalso
       length kept = length fixtures)
    val _ = expect "empty lambda mode is rejected outside the legacy path"
      ((ignore (hhLamTrans.mode_of_string ""); false)
       handle Fail _ => true)
    val _ = expect "lambda mode names round trip"
      (List.all (fn mode =>
         hhLamTrans.mode_of_string (hhLamTrans.mode_name mode) = mode)
         [hhLamTrans.Lifting, hhLamTrans.Combs, hhLamTrans.CombsAndLifting,
          hhLamTrans.KeepLams])
  in
    ()
  end

val _ = test_hhLamTrans ()

fun test_hhMonomorph () =
  let
    open boolSyntax
    val alpha = Type.alpha
    val beta = Type.beta
    val num = Term.type_of ``0 : num``
    fun list_ty ty = Type.mk_type ("list", [ty])
    fun pair_ty left right = Type.mk_type ("prod", [left, right])
    fun nil_tm ty = Term.inst [{redex = alpha, residue = ty}] ``[]``
    fun eq_nil ty = mk_eq (nil_tm ty, nil_tm ty)
    fun conjs [] = boolSyntax.T
      | conjs (first :: rest) = List.foldl (fn (tm, result) =>
          mk_conj (result, tm)) first rest
    fun named name facts =
      List.filter (fn (other, _) => other = name) facts
    fun same_output left right =
      ListPair.allEq (fn ((left_name, left_tm), (right_name, right_tm)) =>
        left_name = right_name andalso Term.aconv left_tm right_tm)
        (left, right)
    val goal = eq_nil (list_ty num)
    val schematic = eq_nil (list_ty alpha)
    val expected = Term.inst [{redex = alpha, residue = num}] schematic
    val basic = hhMonomorph.monomorph
      {max_iters = 3, max_new_instances = 100} goal
      [("ground", goal), ("schematic", schematic)]
    val predicate = Term.mk_var ("P", Type.mk_type ("fun", [alpha,
      Type.bool]))
    val x = Term.mk_var ("X", alpha)
    val ignored = Term.mk_comb (predicate, x)
    val with_ignored = hhMonomorph.monomorph
      {max_iters = 3, max_new_instances = 100} goal
      [("ground", goal), ("ignored", ignored), ("schematic", schematic)]
    val global_cap = hhMonomorph.monomorph
      {max_iters = 3, max_new_instances = 1} goal
      [("first", schematic), ("second", schematic)]
    fun nested 0 = num
      | nested count = list_ty (nested (count - 1))
    val cap_goal = conjs (map (fn index =>
      eq_nil (list_ty (nested index))) (List.tabulate (11, fn index => index)))
    val per_fact = hhMonomorph.monomorph
      {max_iters = 3, max_new_instances = 100} cap_goal
      [("many", schematic)]
    val smallest_ten = map (fn index =>
      Term.inst [{redex = alpha, residue = nested index}] schematic)
      (List.tabulate (10, fn index => index))
    val too_many_predicate = Term.mk_var ("Q",
      List.foldr (fn (_, ty) => Type.mk_type ("fun", [list_ty alpha, ty]))
        Type.bool (List.tabulate (21, fn index => index)))
    val too_many = Term.list_mk_comb (too_many_predicate,
      List.tabulate (21, fn _ => nil_tm alpha))
    val schematic_cap = hhMonomorph.monomorph
      {max_iters = 3, max_new_instances = 100} goal
      [("too-many", too_many)]
    val pair_alpha_num = pair_ty alpha num
    val pair_beta_num = pair_ty beta num
    val chain = conjs [eq_nil (list_ty alpha),
      eq_nil (list_ty pair_alpha_num)]
    val downstream = eq_nil (list_ty pair_beta_num)
    val one_round = hhMonomorph.monomorph
      {max_iters = 1, max_new_instances = 100} goal
      [("chain", chain), ("downstream", downstream)]
    val privileged = hhMonomorph.monomorph
      {max_iters = 2, max_new_instances = 100} goal
      [("chain", chain), ("downstream", downstream)]
    val filler = List.tabulate (10, fn index =>
      ("filler" ^ Int.toString index, goal))
    val late_facts = filler @ [("chain", chain),
      ("downstream", downstream)]
    val late = hhMonomorph.monomorph
      {max_iters = 3, max_new_instances = 100} goal late_facts
    (* Round 2 joins the goal's grounds (initial table) with the round 1
       instances of a privileged fact: 'a comes from the goal, 'b from the
       seed.  Using only the new or only the known table loses one. *)
    fun none_tm ty = Term.inst [{redex = alpha, residue = ty}] ``NONE``
    fun eq_none ty = mk_eq (none_tm ty, none_tm ty)
    val goal2 = conjs [eq_nil (list_ty num), eq_none Type.bool]
    val filler2 = List.tabulate (9, fn index =>
      ("filler" ^ Int.toString index, goal2))
    val join_seed = conjs [eq_nil (list_ty alpha),
      eq_nil (list_ty (pair_ty alpha alpha))]
    val join = conjs [eq_none beta, eq_nil (list_ty (pair_ty alpha alpha))]
    val join_facts = [("seed", join_seed)] @ filler2 @ [("join", join)]
    val joined = hhMonomorph.monomorph
      {max_iters = 2, max_new_instances = 100} goal2 join_facts
    val joined_expected = Term.inst [{redex = alpha, residue = num},
                                     {redex = beta, residue = Type.bool}] join
    val early_join = hhMonomorph.monomorph
      {max_iters = 1, max_new_instances = 100} goal2 join_facts
    (* Round 3 reads the table merged in round 2 as its known grounds. *)
    val goal3 = goal2
    val filler3 = List.tabulate (10, fn index =>
      ("filler" ^ Int.toString index, goal3))
    val chain3 = conjs [eq_nil (list_ty alpha),
      eq_nil (list_ty (pair_ty alpha num))]
    val down3 = conjs [eq_nil (list_ty (pair_ty beta num)), eq_none Type.gamma]
    val handoff = hhMonomorph.monomorph
      {max_iters = 3, max_new_instances = 100} goal3
      (filler3 @ [("chain", chain3), ("down", down3)])
    val ordinary = hhMonomorph.monomorph
      {max_iters = 2, max_new_instances = 100} goal
      (filler @ [("chain", chain), ("downstream", downstream)])
    val again = hhMonomorph.monomorph
      {max_iters = 3, max_new_instances = 100} cap_goal
      [("many", schematic)]
    (* No occurrence below covers both type variables.  This forces the
       exhaustive substitution path whose bounded-best implementation must
       agree with the canonical prefix of the complete Cartesian product. *)
    val branch_types = map nested (List.tabulate (15, fn index => index))
    val branch_goal = conjs (map eq_nil branch_types)
    val branch_schema = conjs [eq_nil alpha, eq_nil beta]
    val bounded_branch = hhMonomorph.monomorph
      {max_iters = 1, max_new_instances = 10} branch_goal
      [("branch", branch_schema)]
    fun subst_size subst = List.foldl (fn ({residue, ...}, total) =>
      Type.type_size residue + total) 0 subst
    fun subst_pairs subst = Listsort.sort
      (fn ({redex = left, ...}, {redex = right, ...}) =>
        Type.compare (left, right)) subst
    fun reference_compare (left, right) =
      case Int.compare (subst_size left, subst_size right) of
          EQUAL =>
            let
              fun pairs ([], []) = EQUAL
                | pairs ([], _) = LESS
                | pairs (_, []) = GREATER
                | pairs ({redex = lv, residue = lt} :: ls,
                         {redex = rv, residue = rt} :: rs) =
                    (case Type.compare (lv, rv) of
                         EQUAL =>
                           (case Type.compare (lt, rt) of
                                EQUAL => pairs (ls, rs)
                              | order => order)
                       | order => order)
            in
              pairs (subst_pairs left, subst_pairs right)
            end
        | order => order
    val exhaustive_substs = List.concat (map (fn left =>
      map (fn right => [{redex = alpha, residue = left},
                        {redex = beta, residue = right}]) branch_types)
      branch_types)
    val reference_branch = map (fn subst =>
      ("branch", Term.inst subst branch_schema))
      (List.take (Listsort.sort reference_compare exhaustive_substs, 10))
    (* The goal's 'a is a fixed type.  A premise schematic in 'a (or in
       'b) must still be instantiated at it. *)
    val rigid_goal = eq_nil (list_ty alpha)
    val rigid = hhMonomorph.monomorph
      {max_iters = 3, max_new_instances = 100} rigid_goal
      [("same", schematic), ("other", eq_nil (list_ty beta))]
    val _ = expect "monomorphization instantiates at goal type variables"
      (List.exists (fn (_, tm) => Term.aconv tm rigid_goal)
         (named "same" rigid) andalso
       List.exists (fn (_, tm) => Term.aconv tm rigid_goal)
         (named "other" rigid))
    val _ = expect "monomorphization closes the list/num fixture"
      (length (named "ground" basic) = 1 andalso
       List.exists (fn (_, tm) => Term.aconv tm expected)
         (named "schematic" basic))
    val _ = expect "monomorphization drops ignored facts"
      (null (named "ignored" with_ignored) andalso
       ListPair.allEq (fn ((_, actual), (_, expected)) =>
         Term.aconv actual expected) (named "ground" with_ignored,
         [("ground", goal)]))
    val _ = expect "monomorphization enforces its global instance cap"
      (length global_cap = 1)
    val _ = expect "monomorphization enforces ten instances per fact"
      (ListPair.allEq (fn ((_, actual), expected) => Term.aconv actual expected)
        (named "many" per_fact, smallest_ten))
    val _ = expect "monomorphization skips facts with over twenty schematics"
      (null (named "too-many" schematic_cap))
    val _ = expect "monomorphization enforces its round cap"
      (null (named "downstream" one_round))
    val _ = expect "privileged facts advance pair/list chains by one round"
      (not (null (named "downstream" privileged)) andalso
       null (named "downstream" ordinary))
    val _ = expect "ordinary facts advance by one round per round"
      (not (null (named "downstream" late)))
    val _ = expect "round 2 facts match the merged initial and round 1 table"
      (List.exists (fn (_, tm) => Term.aconv tm joined_expected)
         (named "join" joined) andalso null (named "join" early_join))
    val _ = expect "round 3 facts match the table merged in round 2"
      (not (null (named "down" handoff)))
    val _ = expect "monomorphization output order is deterministic"
      (same_output per_fact again)
    val _ = expect
      "bounded-best monomorphization equals exhaustive canonical prefix"
      (same_output bounded_branch reference_branch)
    (* The reusable pool seeds exactly as the goal does. *)
    val caps = {max_iters = 3, max_new_instances = 100}
    fun via_pool goal premises =
      hhMonomorph.monomorph_pool caps (hhMonomorph.mk_pool goal) premises
    fun pool_same goal premises =
      same_output (via_pool goal premises)
        (hhMonomorph.monomorph caps goal premises)
    val gamma = Type.gamma
    val none_bool = Term.inst [{redex = alpha, residue = Type.bool}]
      ``NONE : 'a option``
    val ground_none = mk_eq (none_bool, none_bool)
    val schematic_none = let
      val none = Term.inst [{redex = alpha, residue = beta}]
        ``NONE : 'a option`` in mk_eq (none, none) end
    val xa = Term.mk_var ("x", alpha)
    val self_eq = mk_eq (xa, xa)
    val empty_pool = via_pool goal []
    val joined_pool = via_pool goal [("ground", ground_none),
      ("list", schematic), ("none", schematic_none)]
    fun witness ty = let val f = Term.mk_var ("f", ty) in mk_eq (f, f) end
    val num_fun = Type.mk_type ("fun", [num, num])
    fun extended goal extras premises =
      same_output
        (hhMonomorph.monomorph_pool caps
          (hhMonomorph.extend_pool (hhMonomorph.mk_pool goal) extras)
          premises)
        (hhMonomorph.monomorph caps (list_mk_conj (goal :: extras))
          premises)
    val ext_facts = [("eq", self_eq)]
    fun ext_count goal extras = length (hhMonomorph.monomorph_pool caps
      (hhMonomorph.extend_pool (hhMonomorph.mk_pool goal) extras)
      ext_facts)
    val rigid_goal = mk_conj (eq_nil (list_ty alpha), goal)
    val _ = expect "monomorph pool: empty helper set gives no facts"
      (null empty_pool)
    val _ = expect "monomorph pool equals monomorph (goal-only grounds)"
      (pool_same goal [("ground", goal), ("schematic", schematic)])
    val _ = expect "monomorph pool takes grounds from ground premises"
      (same_output joined_pool
         (hhMonomorph.monomorph caps goal [("ground", ground_none),
           ("list", schematic), ("none", schematic_none)])
       andalso length (named "none" joined_pool) = 1)
    val shared = hhMonomorph.mk_pool goal
    val first_call = hhMonomorph.monomorph_pool caps shared
      [("ground", ground_none), ("none", schematic_none)]
    val second_call = hhMonomorph.monomorph_pool caps shared
      [("none", schematic_none)]
    val _ = expect "monomorph pool does not keep grounds across calls"
      (length (named "none" first_call) = 1 andalso null second_call)
    val lazy_pool = hhMonomorph.mk_pool goal
    val _ = hhMonomorph.monomorph_pool caps lazy_pool []
    val _ = hhMonomorph.monomorph_pool caps lazy_pool [("ground", goal)]
    val untouched = not (hhMonomorph.pool_indexed lazy_pool)
    val _ = hhMonomorph.monomorph_pool caps lazy_pool
      [("schematic", schematic)]
    val _ = expect "monomorph pool indexes only for a schematic premise"
      (untouched andalso hhMonomorph.pool_indexed lazy_pool)
    val rigid_pool = hhMonomorph.mk_pool rigid_goal
    val reused = hhMonomorph.extend_pool rigid_pool
      [witness (list_ty alpha)]
    val rebuilt = hhMonomorph.extend_pool rigid_pool [witness gamma]
    val _ = expect "monomorph pool extension decides without indexing"
      (not (hhMonomorph.pool_indexed rigid_pool)
       andalso not (hhMonomorph.pool_indexed reused)
       andalso not (hhMonomorph.pool_indexed rebuilt))
    val _ = expect "monomorph pool with rigid variables equals monomorph"
      (pool_same rigid_goal [("schematic", schematic), ("none",
        schematic_none), ("ignored", ignored)])
    val _ = expect "monomorph pool extension without extras is the pool"
      (extended goal [] ext_facts)
    val _ = expect "monomorph pool extension adds witness-only grounds"
      (extended goal [witness num_fun] ext_facts
       andalso ext_count goal [witness num_fun] = ext_count goal [] + 1)
    val _ = expect "monomorph pool extension with a rigid variable type"
      (extended rigid_goal [witness (list_ty alpha)] ext_facts
       andalso ext_count rigid_goal [witness (list_ty alpha)]
               = ext_count rigid_goal [] + 1)
    val _ = expect "monomorph pool extension rebuilds for a new type variable"
      (extended rigid_goal [witness gamma] ext_facts
       andalso extended rigid_goal [witness num_fun, witness gamma,
                                    witness (list_ty alpha)] ext_facts
       andalso ext_count rigid_goal [witness gamma]
               = ext_count rigid_goal [] + 1)
  in
    ()
  end

val _ = test_hhMonomorph ()

(* Legacy FOF lifts the test of an if-then-else to a new variable F0.  As
   an axiom, !F0. (!x y. F0 x y <=> x = y) ==> .. is usable only once a
   prover builds such an F0; the definition must be existential there. *)
fun test_hhTranslate_lifted_axioms () =
  let
    open boolSyntax
    val lifted = ``!x y:num. g x y = if x = y then 1 else 0n``
    val plain = ``!x:num. x + 0 = x``
    val as_axiom = hhTranslate.translate_axiom lifted
    val as_conjecture = hhTranslate.translate lifted
    val (axiom_vars, axiom_body) = strip_exists as_axiom
    val (conjecture_vars, conjecture_body) = strip_forall as_conjecture
  in
    expect "legacy FOF defines lifted terms existentially in axioms"
      (length axiom_vars = 1 andalso is_conj axiom_body andalso
       Term.aconv (rand axiom_body) (rand conjecture_body));
    expect "legacy FOF keeps lifted definitions universal in conjectures"
      (length conjecture_vars = 1 andalso is_imp conjecture_body);
    expect "legacy FOF translates unlifted axioms unchanged"
      (Term.aconv (hhTranslate.translate_axiom plain)
         (hhTranslate.translate plain))
  end

val _ = test_hhTranslate_lifted_axioms ()

fun test_hhProblemGen () =
  let
    open boolSyntax hhTptpProblem hhProblemGen
    val num = Term.type_of ``0 : num``
    val unary_num = Type.mk_type ("fun", [num, num])
    val bool_to_bool = Type.mk_type ("fun", [Type.bool, Type.bool])
    val x = Term.mk_var ("X", num)
    val y = Term.mk_var ("Y", num)
    val f = Term.mk_var ("F", unary_num)
    val p = Term.mk_var ("P", Type.bool)
    val use = Term.mk_var ("use", Type.mk_type
      ("fun", [bool_to_bool, Type.bool]))
    val use_bool = Term.mk_var ("use_bool", bool_to_bool)
    val use_num = Term.mk_var ("use_num", Type.mk_type
      ("fun", [num, Type.bool]))
    val alpha = Type.alpha
    fun list_ty ty = Type.mk_type ("list", [ty])
    fun nil_tm ty = Term.inst [{redex = alpha, residue = ty}] ``[]``
    fun eq_nil ty = mk_eq (nil_tm ty, nil_tm ty)
    val fof = FOF
    val tf0 = TFF {poly = false, fool = NoFool}
    val tx0 = TFF {poly = false,
                   fool = Fool {with_ite = true, with_let = true}}
    val th0 = THF {poly = false,
                   syntax = {with_ite = false, with_let = false},
                   choice = false}
    val th1 = THF {poly = true,
                   syntax = {with_ite = true, with_let = false},
                   choice = false}
    fun input conjecture : named_terms = {conjecture = conjecture, facts = []}
    fun head_name tm =
      let
        fun head body = if Term.is_comb body then head (Term.rator body)
                        else body
        val head = head tm
      in
        if Term.is_var head then #1 (Term.dest_var head)
        else #1 (Term.dest_const head)
      end
    fun proxied_atom format tm =
      let
        val ir = formula_skeleton (input tm)
      in
        case #conjecture (introduce_proxies format ir) of
            HAtom result => result
          | _ => raise Fail "expected atom"
      end
    val beta = Term.mk_comb (Term.mk_abs (x, x), y)
    val eta = Term.mk_abs (x, Term.mk_comb (f, x))
    val let_tm = mk_let (Term.mk_abs (x, Term.mk_comb (f, x)), y)
    val cond_tm = mk_cond (p, x, y)
    val beta_result = #conjecture (presimp fof (input beta))
    val eta_result = #conjecture (presimp fof (input eta))
    val let_fof = #conjecture (presimp fof (input let_tm))
    val let_tx0 = #conjecture (presimp tx0 (input let_tm))
    val cond_tf0 = #conjecture (presimp tf0 (input cond_tm))
    val cond_tx0 = #conjecture (presimp tx0 (input cond_tm))
    val lambda = mk_eq (Term.mk_abs (x, x), Term.mk_abs (x, x))
    val downgraded = pass_lambda tf0 hhLamTrans.KeepLams (input lambda)
    val kept = pass_lambda th0 hhLamTrans.KeepLams (input lambda)
    val goal = eq_nil (list_ty num)
    val schematic = eq_nil (list_ty alpha)
    val mono = pass_monomorph (hhTypeEnc.of_string "mono_native")
      {max_iters = 3, max_new_instances = 100}
      {conjecture = goal, facts = [("schematic", schematic)]}
    val poly = pass_monomorph (hhTypeEnc.of_string "poly_native")
      {max_iters = 3, max_new_instances = 100}
      {conjecture = goal, facts = [("schematic", schematic)]}
    val iff = formula_skeleton (input (mk_eq (mk_neg p, p)))
    val logical_argument = Term.mk_comb (use, negation)
    val applied_not = Term.mk_comb (use_bool, mk_neg p)
    val applied_eq = Term.mk_comb (use_bool, mk_eq (x, y))
    val ite_atom = Term.mk_comb (use_num, cond_tm)
    val _ = expect "hhProblemGen presimp beta-contracts"
      (Term.aconv beta_result y)
    val _ = expect "hhProblemGen presimp eta-contracts"
      (Term.aconv eta_result f)
    val _ = expect "hhProblemGen presimp unfolds LET in every format"
      (Term.aconv let_fof (Term.mk_comb (f, y)) andalso
       Term.aconv let_tx0 (Term.mk_comb (f, y)))
    val _ = expect "hhProblemGen presimp retains COND for helper routing"
      (is_cond cond_tf0 andalso is_cond cond_tx0)
    val _ = expect "hhProblemGen downgrades keep_lams outside THF"
      (not (null (#facts downgraded)) andalso null (#facts kept))
    val poly_pool = hhMonomorph.mk_pool schematic
    val pool_dispatch = pass_monomorph_pool
      (hhTypeEnc.of_string "poly_native")
      {max_iters = 3, max_new_instances = 100}
      poly_pool
      [("schematic", schematic)]
    val _ = expect "hhProblemGen poly encodings bypass the ground pool"
      (not (hhMonomorph.pool_indexed poly_pool) andalso
       ListPair.allEq (fn ((left_name, left), (right_name, right)) =>
         left_name = right_name andalso Term.aconv left right)
         (pool_dispatch, [("schematic", schematic)]))
    val _ = expect "hhProblemGen dispatches monomorphization by encoding"
      (List.exists (fn (_, tm) => not (Term.aconv tm schematic)) (#facts mono)
       andalso ListPair.allEq (fn ((left_name, left), (right_name, right)) =>
         left_name = right_name andalso Term.aconv left right)
         (#facts poly, [("schematic", schematic)]))
    val _ = expect "hhProblemGen skeleton maps boolean equality to iff"
      (case iff of
           {conjecture = HConn (Iff, [HConn (Not, _), HAtom _]), ...} => true
         | _ => false)
    val _ = expect "hhProblemGen uses proxies in FOF and TF0 term positions"
      (head_name (rand (proxied_atom fof logical_argument)) = "pxy.not" andalso
       head_name (rand (proxied_atom tf0 logical_argument)) = "pxy.not")
    val _ = expect "hhProblemGen uses logical proxies in term positions"
      (head_name (rand (proxied_atom tx0 applied_not)) = "pxy.not" andalso
       head_name (rand (proxied_atom tx0 applied_eq)) = "pxy.eq" andalso
       head_name (rand (proxied_atom th0 logical_argument)) = "pxy.not")
    val _ = expect "hhProblemGen gates $ite on the format syntax"
      (head_name (rand (proxied_atom tx0 ite_atom)) = "$ite" andalso
       is_cond (rand (proxied_atom tf0 ite_atom)))
    val proxy_ir = introduce_proxies fof
      (formula_skeleton (input logical_argument))
    val _ = expect "hhProblemGen records used proxies"
      (#proxies proxy_ir = ["not"])
    (* The conjecture uses the not proxy and a later fact the eq proxy, so
       the recorded list must be in first-seen order across both. *)
    val proxy_order_input : named_terms =
      {conjecture = applied_not, facts = [("eq_fact", applied_eq)]}
    val _ = expect "hhProblemGen records proxies in first-seen order"
      (#proxies (introduce_proxies fof
         (formula_skeleton proxy_order_input)) = ["not", "eq"])
    val _ = expect "hhProblemGen composes its front-end passes"
      (#proxies (translate_front
        {format = fof, type_enc = hhTypeEnc.of_string "mono_guards",
         lam_trans = hhLamTrans.Lifting, mono_iters = 3, mono_instances = 100}
        (input logical_argument)) = ["not"] andalso
       #proxies (translate_front
        {format = fof, type_enc = hhTypeEnc.of_string "mono_guards",
         lam_trans = hhLamTrans.Lifting, mono_iters = 3, mono_instances = 100}
        proxy_order_input) = ["not", "eq"])
    fun problem format encoding terms =
      string_of_problem format "hhProblemGen pass 6--8"
        (generate_problem
          {format = format, type_enc = hhTypeEnc.of_string encoding,
           lam_trans = hhLamTrans.Lifting, mono_iters = 3,
           mono_instances = 100}
          terms)
    fun occurrences needle text =
      let
        fun loop haystack count =
          case Substring.position needle haystack of
              (_, rest) =>
                if Substring.isEmpty rest then count
                else loop (Substring.triml (size needle) rest) (count + 1)
      in
        loop (Substring.full text) 0
      end
    val binary_num = Type.mk_type ("fun", [num, unary_num])
    val pxy_f = Term.mk_var ("pxy.f", binary_num)
    val number_pred = Term.mk_var ("NPred", Type.mk_type
      ("fun", [num, Type.bool]))
    val function_var = Term.mk_var ("H", unary_num)
    val function_pred = Term.mk_var ("FPred", Type.mk_type
      ("fun", [unary_num, Type.bool]))
    val full_f = Term.list_mk_comb (pxy_f, [x, y])
    val full_formula = Term.mk_comb (number_pred, full_f)
    val no_function_variable =
      problem fof "mono_guards" {conjecture = full_formula, facts = []}
    val with_function_variable = problem fof "mono_guards"
      {conjecture = mk_forall (function_var, full_formula), facts = []}
    val bool_term = problem fof "mono_guards" (input applied_not)
    val fool_bool_term = problem tx0 "mono_native_fool" (input applied_not)
    val tf1 = TFF {poly = true, fool = NoFool}
    val poly_goal = eq_nil (list_ty alpha)
    val poly_native = problem tf1 "poly_native" (input poly_goal)
    val mono_native = problem tf0 "mono_native" (input poly_goal)
    val higher_native = problem th0 "mono_native_higher" (input poly_goal)
    val higher_fool = problem th0 "mono_native_higher_fool" (input poly_goal)
    val one_ty = Type.mk_type ("one", [])
    val one_x = Term.mk_var ("OX", one_ty)
    val one_y = Term.mk_var ("OY", one_ty)
    val one_naked = mk_forall (one_x,
      mk_forall (one_y, mk_eq (one_x, one_x)))
    val guards_all = problem fof "mono_guards" (input one_naked)
    val guards_query = problem fof "mono_guards??" (input one_naked)
    val one_only = mk_forall (one_x, mk_eq (one_x, one_x))
    val one_all = problem fof "mono_guards" (input one_only)
    val one_query = problem fof "mono_guards??" (input one_only)
    val forty_four = problem tf1 "poly_native"
      {conjecture = full_formula,
       facts = List.tabulate (44, fn index =>
         ("f" ^ Int.toString index,
          Term.mk_comb (function_pred, Term.mk_comb (pxy_f, x))))}
    val forty_five = problem tf1 "poly_native"
      {conjecture = full_formula,
       facts = List.tabulate (45, fn index =>
         ("f" ^ Int.toString index,
          Term.mk_comb (function_pred, Term.mk_comb (pxy_f, x))))}
    val _ = expect "hhProblemGen respects final application arities"
      (String.isSubstring "pxy_2Ef(" no_function_variable andalso
       not (String.isSubstring "app_2E(pxy_2Ef" no_function_variable) andalso
       String.isSubstring "app_2E(pxy_2Ef" with_function_variable)
    val _ = expect "hhProblemGen switches to Min_App_Op at forty-five facts"
      (occurrences "app_2E(pxy_2Ef" forty_four = 44 andalso
       occurrences "app_2E(pxy_2Ef" forty_five = 45)
    (* The COND conjecture adds six helpers (if_True, if_False, bool_cases,
       pxy.true, pxy.false, eq_ext) after the main facts, so 38 user facts
       give 44 facts at firstorderize and 39 give 45.  The helpers alone then
       decide whether Min_App_Op applies. *)
    fun pxy_facts count = List.tabulate (count, fn index =>
      ("f" ^ Int.toString index,
       Term.mk_comb (function_pred, Term.mk_comb (pxy_f, x))))
    val cond_conjecture = mk_conj (full_formula, mk_eq (cond_tm, x))
    val below_threshold = problem tf1 "poly_native"
      {conjecture = cond_conjecture, facts = pxy_facts 38}
    val crossing_threshold = problem tf1 "poly_native"
      {conjecture = cond_conjecture, facts = pxy_facts 39}
    val _ = expect "hhProblemGen recomputes arities when helpers cross 45"
      (occurrences "app_2E(pxy_2Ef" below_threshold = 1 andalso
       occurrences "app_2E(pxy_2Ef" crossing_threshold = 39)
    val z = Term.mk_var ("Z", num)
    val ternary_num = Type.mk_type ("fun", [num, binary_num])
    (* pxy.s and pxy.t take three arguments; pxy.t is over-applied, so the main
       problem uses app and gets the eq_ext helper. *)
    val pxy_s = Term.mk_var ("pxy.s", ternary_num)
    val pxy_t = Term.mk_var ("pxy.t", ternary_num)
    val pred_unary = Term.mk_var ("PU", Type.mk_type ("fun",
      [unary_num, Type.bool]))
    val pred_binary = Term.mk_var ("PB", Type.mk_type ("fun",
      [binary_num, Type.bool]))
    val helper_arity_goal = boolSyntax.list_mk_conj
      [Term.mk_comb (pred_unary, Term.list_mk_comb (pxy_s, [x, y])),
       mk_eq (Term.list_mk_comb (pxy_s, [x, y, z]), x),
       Term.mk_comb (pred_binary, Term.mk_comb (pxy_t, x)),
       mk_eq (Term.list_mk_comb (pxy_t, [x, y, z]), x)]
    val helper_arity = problem tf0 "mono_native" (input helper_arity_goal)
    (* Only the eq_ext helper quantifies over a function of type
       num -> num -> num, which is the result type of pxy.s after one
       argument.  Its presence lowers the application arity of the main
       symbol pxy.s from two to one. *)
    val _ = expect "hhProblemGen lets helper variables lower main arities"
      (String.isSubstring "pxy_2Es : ty_2Enum_2Enum > " helper_arity andalso
       String.isSubstring "pxy_2Es(X)" helper_arity andalso
       not (String.isSubstring "pxy_2Es(X,Y)" helper_arity))
    val _ = expect "hhProblemGen inserts pp for non-FOOL boolean terms"
      (String.isSubstring "pp_2E(app_2E" bool_term andalso
       not (String.isSubstring "pp_2E(app_2E" fool_bool_term))
    val _ = expect
      "hhProblemGen mangles mono symbols, sorts, and type variables"
      (String.isSubstring "c_2Elist_2ENIL" mono_native andalso
       String.isSubstring "ty_2E" mono_native andalso
       String.isSubstring "var_2E_27a" mono_native)
    val _ = expect
      "hhProblemGen binds TF1 type variables and emits declarations"
      (String.isSubstring "!>[A" poly_native andalso
       String.isSubstring "tff(ty_" poly_native andalso
       String.isSubstring "tff(sy_" poly_native)
    val _ = expect "all native encoding paths produce TPTP structures"
      (String.isSubstring "tff(conjecture" mono_native andalso
       String.isSubstring "tff(conjecture" fool_bool_term andalso
       String.isSubstring "thf(conjecture" higher_native andalso
       String.isSubstring "thf(conjecture" higher_fool)
    val _ = expect "monomorphic THF flattens applied types to ground sorts"
      (String.isSubstring
         "ty_2Elist_2Elist_28var_2E_27a_29 : $tType" higher_native)
    val _ = expect "mono_guards?? guards fewer naked variables"
      (occurrences "gd_2E" guards_query < occurrences "gd_2E" guards_all)
    val _ = expect "mono_guards?? agrees on possibly-finite naked types"
      (String.isSubstring "![OX]: (gd_2E" one_query andalso
       String.isSubstring "![OX]: (gd_2E" one_all)
    val _ = expect "hhProblemGen emits result guards and witnesses"
      (String.isSubstring "gsy_2E" bool_term andalso
       String.isSubstring "wit_2E" guards_all)
    val cond_helpers = problem tf0 "mono_native"
      (input (mk_eq (cond_tm, x)))
    val app_helpers = with_function_variable
    val pp_helpers = bool_term
    val no_helpers = problem fof "mono_guards" (input (mk_eq (x, x)))
    val _ = expect "hhProblemGen injects all COND helpers iff COND occurs"
      (String.isSubstring "help_2Eif__True" cond_helpers andalso
       String.isSubstring "help_2Eif__False" cond_helpers andalso
       String.isSubstring "help_2Ebool__cases" cond_helpers andalso
       not (String.isSubstring "help_2Eif__True" no_helpers) andalso
       not (String.isSubstring "help_2Eif__False" no_helpers))
    (* Through pp, b = T as an iff is a tautology; bool_cases must be a
       term equation, or a test such as X = Y never reaches if_True. *)
    val cond_guards = problem fof "mono_guards"
      (input (mk_eq (cond_tm, x)))
    val _ = expect "hhProblemGen states bool_cases as term equations"
      (String.isSubstring "((HB = pxy_2Etrue) | (HB = pxy_2Efalse))"
         cond_helpers andalso
       String.isSubstring "((HB = pxy_2Etrue) | (HB = pxy_2Efalse))"
         cond_guards)
    val _ = expect "hhProblemGen injects EQ_EXT iff app occurs"
      (String.isSubstring "help_2Eeq__ext" app_helpers andalso
       not (String.isSubstring "help_2Eeq__ext" no_helpers))
    val _ = expect "hhProblemGen injects pp laws iff pp occurs"
      (String.isSubstring "help_2Epp_2Etrue" pp_helpers andalso
       String.isSubstring "help_2Epp_2Efalse" pp_helpers andalso
       not (String.isSubstring "help_2Epp_2Etrue" no_helpers) andalso
       not (String.isSubstring "help_2Epp_2Efalse" no_helpers))
    val quantifier_use = Term.mk_var ("quantifier_use", Type.mk_type
      ("fun", [Term.type_of universal, Type.bool]))
    val all_helpers = problem fof "mono_guards"
      (input (Term.mk_comb (quantifier_use, universal)))
    val ex_helpers = problem fof "mono_guards"
      (input (Term.mk_comb (quantifier_use, existential)))
    val true_helpers = problem fof "mono_guards"
      (input (Term.mk_comb (use_bool, T)))
    val false_helpers = problem fof "mono_guards"
      (input (Term.mk_comb (use_bool, F)))
    fun logical_helper constant =
      let val use = Term.mk_var ("logical_helper",
        Type.mk_type ("fun", [Term.type_of constant, Type.bool])) in
        problem fof "mono_guards" (input (Term.mk_comb (use, constant)))
      end
    (* A top-level equation is TPTP equality; one under a symbol needs the
       pxy.eq proxy and its laws. *)
    val eq_helpers = problem fof "mono_guards"
      (input (Term.mk_comb (use_bool, mk_eq (x, x))))
    val conj_helpers = logical_helper conjunction
    val disj_helpers = logical_helper disjunction
    val imp_helpers = logical_helper implication
    val _ = expect "hhProblemGen injects proxy laws iff their proxies occur"
      (String.isSubstring "help_2Epxy_2Eeq" eq_helpers andalso
       not (String.isSubstring "help_2Epxy_2Eeq" no_helpers) andalso
       String.isSubstring "help_2Epxy_2Enot" pp_helpers andalso
       String.isSubstring "help_2Epxy_2Econj" conj_helpers andalso
       String.isSubstring "help_2Epxy_2Edisj" disj_helpers andalso
       String.isSubstring "help_2Epxy_2Eimp" imp_helpers andalso
       String.isSubstring "help_2Epxy_2Eall" all_helpers andalso
       String.isSubstring "help_2Epxy_2Eex" ex_helpers andalso
       String.isSubstring "help_2Epxy_2Etrue" true_helpers andalso
       String.isSubstring "help_2Epxy_2Efalse" false_helpers andalso
       not (String.isSubstring "help_2Epxy_2Eall" no_helpers) andalso
       not (String.isSubstring "help_2Epxy_2Eex" no_helpers))
    (* Combs mode retains schematic proxy laws that have no instance. *)
    val poly_universal = boolSyntax.universal
    val poly_quantifier_use = Term.mk_var ("poly_quantifier_use",
      Type.mk_type ("fun", [Term.type_of poly_universal, Type.bool]))
    val combs_all = string_of_problem tf0 "combs pool"
      (generate_problem
        {format = tf0, type_enc = hhTypeEnc.of_string "mono_native",
         lam_trans = hhLamTrans.Combs, mono_iters = 3, mono_instances = 100}
        (input (Term.mk_comb (poly_quantifier_use, poly_universal))))
    (* A rigid type variable keeps the proxy laws at its function types
       (pxy.all at several types) and EQ_EXT at app's types, all through
       the pool of the main problem. *)
    val _ = expect "hhProblemGen combs mono helpers use the pool with tyvars"
      (String.isSubstring "help_2Epxy_2Eall," combs_all andalso
       String.isSubstring "help_2Epxy_2Eall_2E2" combs_all andalso
       String.isSubstring "help_2Eeq__ext_2E2" combs_all andalso
       String.isSubstring "var_2E_27a" combs_all)
    val memo = new_export_memo ()
    val output1 = OS.FileSys.tmpName ()
    val output2 = OS.FileSys.tmpName ()
    val export_options =
      {format = tf0, type_enc = hhTypeEnc.of_string "mono_native",
       lam_trans = hhLamTrans.Lifting, mono_iters = 3, mono_instances = 100}
    val theorem = DB.fetch "bool" "TRUTH"
    val exported = (``free_goal:bool`` : Term.term, [("truth", theorem)])
    val _ = export_pb_in memo export_options output1 exported
    val _ = export_pb_in memo export_options output2 exported
    val first_export = String.concat (read_lines output1)
    val second_export = String.concat (read_lines output2)
    val _ = OS.FileSys.remove output1
    val _ = OS.FileSys.remove output2
    val _ = expect "hhProblemGen export is stable and memoizes lambda handling"
      (first_export = second_export andalso memo_lambda_runs memo = 1 andalso
       String.isSubstring "% generated by hhProblemGen; format=tff"
         first_export andalso
       String.isSubstring "% Declarations" first_export andalso
       String.isSubstring "% Helpers" first_export andalso
       String.isSubstring "% Facts" first_export andalso
       String.isSubstring "% Conjecture" first_export)
    val comb_problem = string_of_problem tf0 "combin helpers"
      (generate_problem
        {format = tf0, type_enc = hhTypeEnc.of_string "mono_native",
         lam_trans = hhLamTrans.Combs, mono_iters = 3, mono_instances = 100}
        (input lambda))
    val _ = expect "hhProblemGen fetches combinator helpers only for combs"
      (String.isSubstring "help_2Ecombin_2EI" comb_problem andalso
       not (String.isSubstring "help_2Ecombin_2EI" mono_native))
    (* This exporter fixture has a polymorphic premise and puts lambdas,
       COND, a Boolean term in term position, and naked equality in its
       conjecture.  It is deliberately proof-independent. *)
    val golden_goal = mk_conj (mk_eq (cond_tm, x),
      mk_conj (lambda, mk_conj (applied_not, mk_eq (x, x))))
    val golden_exported = (golden_goal, [("poly", Thm.REFL schematic)])
    val golden_specs =
      [("hhproblemgen-tx0-lifting.p", tx0, "mono_native_fool", "lifting"),
       ("hhproblemgen-tx0minus-lifting.p",
        TFF {poly = false, fool = Fool {with_ite = false, with_let = false}},
        "mono_native_fool", "lifting"),
       ("hhproblemgen-th1-keep-lams.p", th1, "mono_native_higher_fool",
        "keep_lams"),
       ("hhproblemgen-th0-keep-lams.p", th0, "mono_native_higher",
        "keep_lams"),
       ("hhproblemgen-tf1-lifting.p", tf1, "poly_native", "lifting"),
       ("hhproblemgen-tf0-combs-lifting.p", tf0, "mono_native",
        "combs_and_lifting"),
       ("hhproblemgen-tx0-combs.p", tx0, "mono_native_fool", "combs"),
       ("hhproblemgen-fof-guards-query.p", fof, "mono_guards??", "lifting")]
    (* Type order fixture.  Types are collected from the last premise
       back to the conjecture.  The last premise is a curried application
       of a constant, whose first application introduces fresh, deeply
       nested types (no variable binds them first), and the other premises
       add further fresh types, so the visit order of types (function,
       argument, result) and of formulas shows in the type declarations
       and the guard witnesses.  One mono instance keeps the extensionality
       helper, which visits every application type first, off these. *)
    fun opt_ty ty = Type.mk_type ("option", [ty])
    fun fun_ty (domain, range) = Type.mk_type ("fun", [domain, range])
    fun at_type ty tm = Term.inst [{redex = alpha, residue = ty}] tm
    val elem_ty = opt_ty (list_ty (opt_ty num))
    val in_op = at_type elem_ty ``$IN``
    val membership = Term.list_mk_comb (in_op,
      [at_type (list_ty (opt_ty num)) ``NONE``,
       Term.inst [{redex = alpha, residue = fun_ty (elem_ty, Type.bool)}]
         ``ARB``])
    val k = Term.mk_var ("K",
      fun_ty (num, opt_ty (list_ty (list_ty Type.bool))))
    (* A bound variable of IN's type makes its applications partial. *)
    val bound_in = Term.mk_var ("V", Term.type_of in_op)
    val order_exported =
      (p,
       [("k", Thm.REFL (Term.mk_comb (k, y))),
        ("v", Thm.REFL (mk_forall (bound_in, p))),
        ("m", Thm.SPEC membership (DB.fetch "bool" "EXCLUDED_MIDDLE"))])
    fun golden_problem_of exported instances (name, format, encoding, mode) =
      let
        val options =
          {format = format, type_enc = hhTypeEnc.of_string encoding,
           lam_trans = hhLamTrans.mode_of_string mode, mono_iters = 3,
           mono_instances = instances}
        val temporary = OS.FileSys.tmpName ()
        val _ = export_pb options temporary exported
        val actual = String.concat (read_lines temporary)
        val _ = OS.FileSys.remove temporary
        val path = join "test-data/problems" name
      in
        expect_equal ("hhProblemGen golden " ^ name)
          (String.concat (read_lines path)) actual
      end
    val _ = List.app (golden_problem_of golden_exported 100) golden_specs
    (* A bound function-valued variable and one polymorphic constant used
       at two types, against output of the unmemoised encoder. *)
    val symbol_goal = (``(!H : num -> num. H 0 = 0) /\
      (([] : num list) = []) /\ (([] : bool list) = [])``, [])
    val _ = List.app (golden_problem_of symbol_goal 100)
      [("hhproblemgen-tf0-symbols.p", tf0, "mono_native", "lifting"),
       ("hhproblemgen-tf1-symbols.p", tf1, "poly_native", "lifting")]
    (* Repeated ordinary names (thm, thm2, thm3), repeated helper names
       (help.h, help.h.2) and the lam. exception (never numbered), against
       pre-change output. *)
    fun copy_fact name n =
      (name, Thm.mk_oracle_thm "hhProblemGen_selftest"
              ([], ``(P : num -> bool) ^(numSyntax.term_of_int n)``))
    val copies_goal = (``(x : num) = x``,
      [copy_fact "a" 1, copy_fact "b" 2, copy_fact "a" 3, copy_fact "a" 4,
       copy_fact "help.h" 5, copy_fact "lam.1" 6, copy_fact "help.h" 7,
       copy_fact "lam.1" 8, copy_fact "b" 9, copy_fact "help.h" 10])
    val _ = List.app (golden_problem_of copies_goal 100)
      [("hhproblemgen-tf0-copies.p", tf0, "mono_native", "lifting"),
       ("hhproblemgen-tf1-copies.p", tf1, "poly_native", "lifting")]
    val _ = List.app (golden_problem_of order_exported 1)
      [("hhproblemgen-tf0-type-order.p", tf0, "mono_native", "lifting"),
       ("hhproblemgen-fof-type-order.p", fof, "mono_guards", "lifting")]
    (* This is export-linked: the fake proof names are the exact escaped
       identifiers the fixture just emitted, including a mono copy. *)
    val roundtrip_name = "fixtureTheory.roundtrip"
    val roundtrip_file = OS.FileSys.tmpName ()
    val roundtrip_theorem = DB.fetch "bool" "TRUTH"
    val roundtrip_input = (mk_conj (mk_eq (cond_tm, x), lambda),
      [(roundtrip_name, roundtrip_theorem),
       (roundtrip_name, roundtrip_theorem)])
    val _ = export_pb export_options roundtrip_file roundtrip_input
    val roundtrip_problem = String.concat (read_lines roundtrip_file)
    val _ = OS.FileSys.remove roundtrip_file
    val escaped_roundtrip = aiLib.escape ("thm." ^ roundtrip_name)
    val escaped_copy = aiLib.escape ("thm2." ^ roundtrip_name)
    val _ = expect
      "hhProblemGen export-linked parse-back fixture emits all names"
      (String.isSubstring escaped_roundtrip roundtrip_problem andalso
       String.isSubstring escaped_copy roundtrip_problem andalso
       String.isSubstring "lam_2E" roundtrip_problem andalso
       String.isSubstring "help_2Eif__True" roundtrip_problem)
    val _ = expect_equal "hhProblemGen export-linked TSTP round trip"
      [roundtrip_name]
      (hhProver.axioms_from_tstp
        ["fof(" ^ escaped_roundtrip ^ ", axiom, p).",
         "fof(" ^ escaped_copy ^ ", axiom, p).",
         "fof(lam_2E0, axiom, p).",
         "fof(help_2Eif__True, axiom, p).",
         "fof(ty_2Efixture, axiom, p).",
         "fof(sy_2Efixture, axiom, p).",
         "fof(gsy_2Efixture, axiom, p).",
         "fof(wit_2Efixture, axiom, p)."])
  in
    ()
  end

val _ = test_hhProblemGen ()

(* let x1 = g x0 x0 in let x2 = g x1 x1 in ... x12: unfolding every LET
   copies each argument twice, 2^12 leaves.  The aliased chain puts
   let y = x in front of each use, which only unfolding the alias first
   shows to copy x.  TX0 has $let syntax, but the generator does not emit
   $let, so a kept LET must be defined there as well. *)
fun test_hhProblemGen_let_chain () =
  let
    open boolSyntax hhTptpProblem
    val depth = 12
    val num = numSyntax.num
    val g = Term.mk_var ("g", Type.--> (num, Type.--> (num, num)))
    val h = Term.mk_var ("h", Type.--> (num, num))
    fun var i = Term.mk_var ("x" ^ Int.toString i, num)
    fun alias i = Term.mk_var ("y" ^ Int.toString i, num)
    fun double tm = Term.list_mk_comb (g, [tm, tm])
    fun chain i =
      if i = depth then var i
      else mk_let (Term.mk_abs (var (i + 1), chain (i + 1)), double (var i))
    fun aliased i =
      if i = depth then var i
      else mk_let
        (Term.mk_abs (alias i,
           mk_let (Term.mk_abs (var (i + 1), aliased (i + 1)),
             double (alias i))),
         var i)
    val p = Term.mk_var ("p", Type.--> (num, Type.bool))
    fun problem (format, encoding) tm =
      string_of_problem format "let chain"
        (hhProblemGen.generate_problem
          {format = format, type_enc = hhTypeEnc.of_string encoding,
           lam_trans = hhLamTrans.Lifting, mono_iters = 3,
           mono_instances = 100}
          {conjecture = Term.mk_comb (p, tm), facts = []})
    (* Unfolded, either chain prints g 2^12 times. *)
    fun translates setting tm =
      let val text = problem setting tm in
        String.size text < 50000 andalso
        String.isSubstring "help_2Ebool_2ELET" text
      end
    val tf0 = (TFF {poly = false, fool = NoFool}, "mono_native")
    val tx0 = (hhTypeEnc.format_of_string "tx0", "mono_native_fool")
    val let_thm = Thm.concl boolTheory.LET_THM
    val single = mk_let (Term.mk_abs (var 0, Term.mk_comb (h, var 0)),
      double (var 1))
  in
    expect "hhProblemGen keeps and defines a chain of copying lets in TF0"
      (translates tf0 (chain 0));
    expect "hhProblemGen keeps and defines a chain of copying lets in TX0"
      (translates tx0 (chain 0));
    expect "hhProblemGen keeps and defines a chain of aliased copying lets"
      (translates tf0 (aliased 0));
    expect "hhProblemGen presimp keeps LET_THM's LET f x"
      (Term.aconv (hhProblemGen.beta_eta_contract true let_thm) let_thm);
    expect "hhProblemGen presimp unfolds a single-use let of a compound value"
      (Term.aconv (hhProblemGen.beta_eta_contract true single)
         (Term.mk_comb (h, double (var 1))))
  end

val _ = test_hhProblemGen_let_chain ()

(* A sort checker for monomorphic TFF problems (TF0 and TX0): every
   symbol has a single declaration and every application, equation, and
   atom is well sorted.  It mirrors the checks Vampire and E apply. *)
fun mono_tff_errors (problem : hhTptpProblem.problem) =
  let
    open hhTptpProblem
    val bool_sort = TyCon ("$o", [])
    fun strip (TyFun (domain, range)) =
          let val (domains, result) = strip range in
            (domain :: domains, result)
          end
      | strip ty = ([], ty)
    val lines = List.concat (map #2 problem)
    val errors = ref ([] : string list)
    fun error message = errors := message :: !errors
    val table = List.foldl (fn (SymDecl (_, symbol, ty), table) =>
        (case Redblackmap.peek (table, symbol) of
             SOME old =>
               (if old = ty then ()
                else error ("conflicting declarations of " ^ symbol);
                table)
           | NONE => Redblackmap.insert (table, symbol, ty))
      | (_, table) => table) (Redblackmap.mkDict String.compare) lines
    fun sort_of env (Tm ((symbol, _), args)) =
          let val arg_sorts = map (sort_of env) args in
            case (List.find (fn (name, _) => name = symbol) env, args) of
                (SOME (_, ty), []) => SOME ty
              | (SOME _, _) => (error ("applied variable " ^ symbol); NONE)
              | (NONE, _) =>
                if symbol = "$true" orelse symbol = "$false" then
                  SOME bool_sort
                else if symbol = "$ite" then
                  (case arg_sorts of
                       [SOME test, SOME left, SOME right] =>
                         if test = bool_sort andalso left = right then
                           SOME left
                         else (error "ill-sorted $ite"; NONE)
                     | _ => NONE)
                else
                  case Redblackmap.peek (table, symbol) of
                      NONE => (error ("undeclared " ^ symbol); NONE)
                    | SOME ty =>
                        let val (domains, result) = strip ty in
                          if length domains = length args andalso
                             ListPair.all (fn (domain, actual) =>
                               actual = NONE orelse actual = SOME domain)
                               (domains, arg_sorts)
                          then SOME result
                          else (error ("ill-sorted application of " ^
                                       symbol); NONE)
                        end
          end
      | sort_of _ (TmAbs _) = (error "lambda in TFF"; NONE)
    fun formula env (Quant (_, bound, body)) =
          formula (map (fn (name, ty) =>
            (name, case ty of SOME ty => ty
                            | NONE => TyCon ("$i", []))) bound @ env) body
      | formula env (TyQuant (_, _, body)) = formula env body
      | formula env (Conn (Equal, [Atom left, Atom right])) =
          (case (sort_of env left, sort_of env right) of
               (SOME left_sort, SOME right_sort) =>
                 if left_sort = right_sort then ()
                 else error "ill-sorted equation"
             | _ => ())
      | formula env (Conn (_, bodies)) = List.app (formula env) bodies
      | formula env (Atom tm) =
          (case sort_of env tm of
               SOME sort =>
                 if sort = bool_sort then () else error "non-Boolean atom"
             | NONE => ())
    val _ = List.app (fn FormLine (_, _, body) => formula [] body
                       | _ => ()) lines
  in
    List.rev (!errors)
  end


(* Lambda lifting runs before monomorphization.  MAP_ID's lifted identity
   is therefore polymorphic, and the conjecture grounds it at num and at
   num -> num; each instance must be a separately declared symbol. *)
fun test_hhProblemGen_mono_sorts () =
  let
    val goal = ``MAP (f : num -> num) l = l /\
                 MAP (g : (num -> num) -> num -> num) fs = fs``
    val terms = {conjecture = goal,
                 facts = [("MAP_ID", Thm.concl (DB.fetch "list" "MAP_ID"))]}
    fun check (format, encoding, mode) =
      let
        val problem = hhProblemGen.generate_problem
          {format = hhTypeEnc.format_of_string format,
           type_enc = hhTypeEnc.of_string encoding,
           lam_trans = hhLamTrans.mode_of_string mode, mono_iters = 3,
           mono_instances = 100} terms
        val errors = mono_tff_errors problem
      in
        tprint ("hhProblemGen " ^ format ^ " " ^ mode ^
                " problem is well sorted");
        if null errors then OK ()
        else die ("FAILED: " ^ String.concatWith "; " errors)
      end
  in
    List.app check
      [("tx0", "mono_native_fool", "lifting"),
       ("tx0-", "mono_native_fool", "combs_and_lifting"),
       ("tf0", "mono_native", "lifting"),
       ("tx0", "mono_native_fool", "combs")]
  end

val _ = test_hhProblemGen_mono_sorts ()

(* The lifted identity is only applied through app at num -> num, and the
   problem has no equality at that type, so monomorphization alone leaves
   EQ_EXT at opaque sorts.  It must be instantiated at app's type. *)
fun test_hhProblemGen_mono_extensionality () =
  let
    open hhTptpProblem
    val goal = ``MAP (\x : num. x) l = l``
    val problem = hhProblemGen.generate_problem
      {format = hhTypeEnc.format_of_string "tx0",
       type_enc = hhTypeEnc.of_string "mono_native_fool",
       lam_trans = hhLamTrans.Lifting, mono_iters = 3,
       mono_instances = 100} {conjecture = goal, facts = []}
    val num_to_num =
      TyCon (aiLib.escape ("ty.min.fun(num.num,num.num)"), [])
    fun ext_at_num (FormLine (name, _, Quant (_, [(_, SOME ty)], _))) =
          String.isPrefix (aiLib.escape "help.eq_ext") name andalso
          ty = num_to_num
      | ext_at_num _ = false
  in
    expect "hhProblemGen instantiates EQ_EXT at mono app types"
      (List.exists ext_at_num (List.concat (map #2 problem)))
  end

val _ = test_hhProblemGen_mono_extensionality ()

(* Generated problems draw schematic and combinator type variables from
   the global Type.gen_tyvar counter.  Their names, compared as strings,
   order differently once the counter gains a digit (99 > 100), and under
   a binding mono_instances cap that order can pick different instances.
   So the bytes are a function of the counter state: the same export is
   reproducible whenever its counter window stays within one digit length
   (also when two windows differ in digit length), and always draws the
   same number of names. *)
(* The fresh-name counter: counter () draws one name and returns its
   number; advance_to target draws names until the next one drawn is
   numbered target; power_above n is the least power of ten above n. *)
fun counter () =
  valOf (Int.fromString (String.extract (Type.dest_vartype
    (Type.gen_tyvar ()), size "%%gen_tyvar%%", NONE)))

(* The same for the term-variable counter (Term.genvar), which a proof
   replay draws from as well. *)
fun genvar_counter () =
  valOf (Int.fromString (String.extract (#1 (Term.dest_var
    (Term.genvar Type.alpha)), size "%%genvar%%", NONE)))

fun advance_to target =
  let
    fun advance n = if n <= 0 then () else (Type.gen_tyvar (); advance (n - 1))
  in advance (target - (counter () + 1)) end

fun power_above n =
  let fun up p = if p > n then p else up (10 * p) in up 10 end

fun test_hhProblemGen_counter_window () =
  let
    open boolSyntax
    val alpha = Type.alpha
    val beta = Type.beta
    val num = Type.mk_type ("num", [])
    fun list_ty ty = Type.mk_type ("list", [ty])
    fun map_at from to = Term.inst
      (Type.match_type (Term.type_of listSyntax.map_tm)
         (Type.--> (Type.--> (from, to), Type.--> (list_ty from, list_ty to))))
      listSyntax.map_tm
    fun map_eq from to =
      let
        val f = Term.mk_var ("f", Type.--> (from, to))
        val l = Term.mk_var ("l", list_ty from)
        val tm = Term.list_mk_comb (map_at from to, [f, l])
      in mk_eq (tm, tm) end
    val goal = list_mk_conj (map (fn (from, to) => map_eq from to)
      [(num, Type.bool), (Type.bool, num), (num, num), (alpha, num),
       (num, alpha), (alpha, beta)])
    val premises = [("MAP_APPEND", DB.fetch "list" "MAP_APPEND")]
    val options = {format = hhTypeEnc.format_of_string "tf0",
      type_enc = hhTypeEnc.of_string "mono_native",
      lam_trans = hhLamTrans.Combs, mono_iters = 3, mono_instances = 3}
    val power = power_above (counter () + 2000)
    fun export start =
      let
        val file = OS.FileSys.tmpName ()
        fun finish () = OS.FileSys.remove file handle _ => ()
        val _ = advance_to start
        val first = counter ()
        val used_text =
          (hhProblemGen.export_pb options file (goal, premises);
           (counter () - first - 1, String.concat (read_lines file)))
          handle e => (finish (); raise e)
      in
        finish (); used_text
      end
    (* The first window ends below the next power of ten; the second
       starts just above it, so its names have one more digit. *)
    val (used1, text1) = export (power - 1500)
    val (used2, text2) = export (power + 10)
  in
    expect "hhProblemGen counter window: same bytes and name count"
      (text1 = text2 andalso used1 = used2 andalso used1 > 0)
  end

val _ = test_hhProblemGen_counter_window ()

(* A "lambda survived" failure of the tail of a prepared problem is raised
   raw (it may run on a worker, where the term grammar must not be read)
   and becomes the text the caller-side first-orderization raises, written
   out here as it was before the move. *)
fun test_hhProblemGen_lambda_survived_text () =
  let
    val tm = ``\x:num. x + 1``
    val shown = Parse.term_to_string tm
    val base = "hhProblemGen: lambda survived first-order lambda handling: "
      ^ shown
    fun text exn = (raise exn) handle Fail message => message
    fun described labels =
      text (hhProblemGen.describe_failure
              (hhProblemGen.Lambda_survived (labels, tm)))
    fun forced exn = text (hhProblemGen.describe_failure exn)
    fun forced_tail labels =
      (ignore (hhProblemGen.force_tail (fn () =>
         raise hhProblemGen.Lambda_survived (labels, tm))); "no failure")
      handle Fail message => message
    val _ = expect "describe_failure: the text of a conjecture failure"
      (described ["conjecture"] = "hhProblemGen: conjecture: " ^ base)
    val _ = expect "describe_failure: the text of a fact failure"
      (described ["fact lemma"] = "hhProblemGen: fact lemma: " ^ base)
    val _ = expect "describe_failure: the text of a bare failure"
      (described [] = base)
    val _ = expect "describe_failure: nested labels wrap innermost first"
      (described ["fact lemma", "outer"] =
       "hhProblemGen: outer: hhProblemGen: fact lemma: " ^ base)
    val _ = expect "force_tail: a tail failure is raised as its text"
      (forced_tail ["conjecture"] = "hhProblemGen: conjecture: " ^ base)
    val _ = expect "describe_failure leaves other exceptions alone"
      (forced (Fail "hhProblemGen: malformed function type") =
         "hhProblemGen: malformed function type" andalso
       (case hhProblemGen.describe_failure Interrupt of
            Interrupt => true | _ => false) andalso
       (case hhProblemGen.describe_failure (Feedback.mk_HOL_ERR "x" "y" "z")
        of Feedback.HOL_ERR _ => true | _ => false))
  in
    ()
  end

val _ = test_hhProblemGen_lambda_survived_text ()

val prover = hhProver.config_of

val sample_request : hhProver.run_request =
  {timeout = 7, problem = "problem.p", extra = ["--extra"],
   debug_dir = NONE}

fun test_recording file parser expected_szs expected_axioms =
  let
    val (szs, axioms) = parser (read_lines (join "test-data" file))
    val _ = expect_equal ("recording status " ^ file) expected_szs szs
  in
    expect_equal ("recording axioms " ^ file) expected_axioms axioms
  end

fun test_szs_status_words () =
  let
    val words =
      ["Theorem", "Unsatisfiable", "CounterSatisfiable", "Satisfiable",
       "GaveUp", "Unknown", "Incomplete", "Timeout", "ResourceOut",
       "MemoryOut", "Forced", "User", "Inappropriate", "NewStatus"]
    val expected =
      [hhProver.SzsTheorem, hhProver.SzsTheorem,
       hhProver.SzsCounterSat, hhProver.SzsSatisfiable,
       hhProver.SzsGaveUp, hhProver.SzsGaveUp, hhProver.SzsGaveUp,
       hhProver.SzsTimeout, hhProver.SzsResourceOut,
       hhProver.SzsResourceOut, hhProver.SzsGaveUp, hhProver.SzsGaveUp,
       hhProver.SzsInappropriate, hhProver.SzsUnknown "NewStatus"]
    val actual = map (fn word =>
      hhProver.szs_of_line ("% SZS status " ^ word ^ " for problem"))
      words
  in
    expect_equal "SZS status words" (map SOME expected) actual
  end

fun test_hhProver () =
  let
    val e = prover Eprover
    val vampire = prover Vampire
    val zipperposition = prover Zipperposition
    val z3 = prover Z3
    val names = map #name (hhProver.all ())
    val _ = expect "all built-in provers"
      (names = ["e", "vampire", "zipperposition", "z3"])
    val _ = expect "built-in configs are named by prover_name"
      (names = map hhConfig.prover_name hhConfig.all_provers)
    val _ = expect "prover names parse back to their provers"
      (List.all (fn p =>
         hhConfig.prover_of_name (hhConfig.prover_name p) = SOME p)
         hhConfig.all_provers andalso
       hhConfig.prover_of_name "eprover" = NONE)
    val _ = expect "default provers are found and non-legacy"
      (List.all (fn p => not (#legacy (prover p)))
       (hhProver.default_provers ()))
    val _ = expect "with_override replaces a config only while it runs"
      (hhProver.with_override Z3 e (fn () => #name (prover Z3) = "e")
       andalso #name (prover Z3) = "z3")
    val _ = test_recording "e-theorem-chatter.out" (#parse_output e)
      hhProver.SzsTheorem (SOME ["keep_name"])
    val _ = test_recording "e-counter-sat.out" (#parse_output e)
      hhProver.SzsCounterSat NONE
    val _ = test_recording "e-gave-up.out" (#parse_output e)
      hhProver.SzsGaveUp NONE
    val _ = test_recording "vampire-theorem.out" (#parse_output vampire)
      hhProver.SzsTheorem (SOME ["keep_name"])
    val _ = test_recording "vampire-counter-sat.out" (#parse_output vampire)
      hhProver.SzsCounterSat NONE
    val _ = test_recording "vampire-timeout.out" (#parse_output vampire)
      hhProver.SzsTimeout NONE
    val _ = test_recording "z3-tptp-theorem.out" (#parse_output z3)
      hhProver.SzsTheorem (SOME ["keep_name"])
    val _ = test_recording "zipperposition-theorem.out"
      (#parse_output zipperposition) hhProver.SzsTheorem
      (SOME ["keep_name"])
    val _ = test_recording "zipperposition-counter-sat.out"
      (#parse_output zipperposition) hhProver.SzsCounterSat NONE
    val _ = test_recording "zipperposition-gave-up.out"
      (#parse_output zipperposition) hhProver.SzsGaveUp NONE
    val _ = test_recording "zipperposition-timeout.out"
      (#parse_output zipperposition) hhProver.SzsResourceOut NONE
    val _ = test_recording "vampire-5.0.1-tx0-lifting.out"
      (#parse_output vampire) hhProver.SzsTheorem
      (SOME ["arithmeticTheory.ADD1"])
    val _ = test_recording "e-3.2.5-ho-tx0minus-lifting.out"
      (#parse_output e) hhProver.SzsTheorem (SOME ["arithmeticTheory.ADD1"])
    val _ = test_recording "zipperposition-2.1-th1-keep-lams.out"
      (#parse_output zipperposition) hhProver.SzsTheorem
      (SOME ["arithmeticTheory.ADD1"])
    val _ = test_recording "e-3.2.5-ho-th0-keep-lams.out"
      (#parse_output e) hhProver.SzsTheorem (SOME ["arithmeticTheory.ADD1"])
    val _ = test_recording "vampire-5.0.1-th0-substitute.out"
      (#parse_output vampire) hhProver.SzsTheorem
      (SOME ["arithmeticTheory.ADD1"])
    val _ = test_recording "e-3.2.5-ho-tx0minus-combs-lifting.out"
      (#parse_output e) hhProver.SzsTheorem (SOME ["arithmeticTheory.ADD1"])
    val _ = test_recording "vampire-5.0.1-tx0-combs.out"
      (#parse_output vampire) hhProver.SzsTheorem
      (SOME ["arithmeticTheory.ADD1"])
    val _ = test_recording "zipperposition-2.1-fof-substitute.out"
      (#parse_output zipperposition) hhProver.SzsTheorem
      (SOME ["arithmeticTheory.ADD1"])
    val _ = expect_equal
      "TSTP parse-back drops generated names and dedups copies"
      ["alpha", "beta"]
      (hhProver.axioms_from_tstp
        (read_lines "test-data/hhproblemgen-roundtrip.out"))
    val _ = expect_equal "TSTP parse-back accepts thm copies and dedups"
      ["alpha"]
      (hhProver.axioms_from_tstp
        ["fof(thm_2Ealpha, axiom, p).",
         "fof(thm2_2Ealpha, axiom, p).",
         "fof(thm10_2Ealpha, axiom, p)."])
    val _ = expect_equal "E version parser" (SOME "3.2.5-ho")
      (#parse_version e (String.concat (read_lines "test-data/e-version.out")))
    val _ = expect_equal "Vampire version parser" (SOME "5.0.1")
      (#parse_version vampire
       (String.concat (read_lines "test-data/vampire-version.out")))
    val _ = expect_equal "Zipperposition version parser" (SOME "2.1")
      (#parse_version zipperposition
       (String.concat (read_lines "test-data/zipperposition-version.out")))
    val _ = expect_equal "Z3 TPTP version parser" (SOME "4.11.2.0")
      (#parse_version z3 "Z3tptp [4.11.2.0] (c) Microsoft Corp.")
    val _ = expect_equal "E command"
      ("e", ["--auto-schedule", "--tstp-in", "--tstp-out", "-s",
             "--cpu-limit=7", "--proof-object=1", "--extra", "problem.p"])
      (#mk_command e "e" sample_request)
    val _ = expect_equal "Vampire command"
      ("vampire", ["--mode", "portfolio", "--schedule", "casc",
        "--input_syntax", "tptp", "--proof", "tptp",
        "--output_axiom_names", "on", "-t", "7", "--extra",
        "--input_file", "problem.p"])
      (#mk_command vampire "vampire" sample_request)
    val _ = expect_equal "Zipperposition command"
      ("zipperposition", ["--input", "tptp", "--output", "tptp",
        "--timeout", "7", "--extra", "problem.p"])
      (#mk_command zipperposition "zipperposition" sample_request)
    val _ = expect_equal "Z3 legacy command"
      ("z3", ["-tptp", "DISPLAY_UNSAT_CORE=true",
        "ELIM_QUANTIFIERS=true", "PULL_NESTED_QUANTIFIERS=true", "-T:7",
        "--extra", "problem.p"])
      (#mk_command z3 "z3" sample_request)
    val _ = expect_equal "Z3 standalone TPTP command"
      ("z3_tptp", ["-c", "-smt.pull_nested_quantifiers:true", "-t:7",
        "--extra", "-file:problem.p"])
      (#mk_command z3 "z3_tptp" sample_request)
  in
    ()
  end

fun slice_options provers slices cores timeout filter max_facts
    : hhConfig.hh_options =
  {timeout = timeout, max_proofs = 4, provers = provers, slices = slices,
   cores = cores,
   export_workers = 1,
   filter = filter, max_facts = max_facts,
   format = "", type_enc = "", lam_trans = "", mono_iters = 3,
   mono_instances = NONE, minimize = true,
   preplay_timeout = 1.0, minimize_timeout = 1.0, cache = false,
   cache_dir = "", cache_max_entries = 100000, debug_dir = NONE,
   preplay_drop_one = false, verbose = false}

fun slice_summary (slice : hhProver.slice) =
  (#prover slice, #format slice, #type_enc slice, #lam_trans slice,
   #nfacts slice, #filter slice, #extra_opts slice, #slice_size slice)

fun schedule_summary
    (schedule : (hhProver.prover_config * hhProver.slice) list) =
  map (fn ((config : hhProver.prover_config),
           (slice : hhProver.slice)) =>
    (#name config, #nfacts slice, #filter slice, #extra_opts slice)) schedule

fun test_hhSlice () =
  let
    fun expected_filter prover format type_enc lam_trans filter nfacts =
      (prover, format, type_enc, lam_trans, nfacts, filter, [], 1)
    fun expected prover format type_enc lam_trans nfacts =
      expected_filter prover format type_enc lam_trans "knn" nfacts
    val phase1 =
      [expected Vampire "fof" "" "" 96,
       expected Eprover "fof" "" "" 128,
       expected Zipperposition "fof" "" "" 128,
       expected Vampire "fof" "" "" 512,
       expected Eprover "fof" "" "" 512,
       expected Vampire "fof" "" "" 32,
       expected Zipperposition "fof" "" "" 512,
       expected Vampire "fof" "" "" 1024]
    val phase2 =
      [expected Vampire "tx0" "mono_native_fool" "lifting" 96,
       expected Eprover "tx0-" "mono_native_fool" "lifting" 128,
       expected Zipperposition "th1" "mono_native_higher_fool"
         "keep_lams" 128,
       expected Eprover "th0" "mono_native_higher" "keep_lams" 512,
       expected Vampire "th0" "mono_native_higher" "lifting" 512,
       expected Eprover "tx0-" "mono_native_fool" "combs_and_lifting" 1024,
       expected Vampire "tx0" "mono_native_fool" "combs" 512,
       expected Zipperposition "fof" "" "" 32]
    val ensemble =
      [expected_filter Vampire "fof" "" "" "mesh" 96,
       expected_filter Eprover "fof" "" "" "mesh" 128,
       expected_filter Zipperposition "th1"
         "mono_native_higher_fool" "keep_lams" "mesh" 128,
       expected_filter Vampire "tx0" "mono_native_fool" "lifting"
         "mesh" 512,
       expected_filter Eprover "fof" "" "" "mepo" 512,
       expected_filter Vampire "fof" "" "" "mepo" 1024,
       expected_filter Eprover "tx0-" "mono_native_fool" "lifting"
         "mash" 128,
       expected_filter Vampire "fof" "" "" "mash" 256]
    val phase2_golden = phase1 @ phase2
    val expected_default = phase2_golden @ ensemble
    val e_slices = map slice_summary (#slices (prover Eprover))
    val vampire_slices = map slice_summary (#slices (prover Vampire))
    val zipperposition_slices =
      map slice_summary (#slices (prover Zipperposition))
    val _ = expect_equal "E slice table"
      [List.nth (phase1, 1), List.nth (phase1, 4),
       List.nth (phase2, 1), List.nth (phase2, 3),
       List.nth (phase2, 5), List.nth (ensemble, 1),
       List.nth (ensemble, 4), List.nth (ensemble, 6)] e_slices
    val _ = expect_equal "Vampire slice table"
      [List.nth (phase1, 0), List.nth (phase1, 3),
       List.nth (phase1, 5), List.nth (phase1, 7),
       List.nth (phase2, 0), List.nth (phase2, 4),
       List.nth (phase2, 6), List.nth (ensemble, 0),
       List.nth (ensemble, 3), List.nth (ensemble, 5),
       List.nth (ensemble, 7)] vampire_slices
    val _ = expect_equal "Zipperposition slice table"
      [List.nth (phase1, 2), List.nth (phase1, 6),
       List.nth (phase2, 2), List.nth (phase2, 7),
       List.nth (ensemble, 2)] zipperposition_slices
    val _ = expect "Z3 stays callable without scheduler slices"
      (List.all (null o (fn config => #slices config))
       (map prover [Z3]))
    val _ = expect_equal "rotation truncates to requested slice count"
      [Vampire, Eprover, Zipperposition, Vampire, Eprover]
      (hhSlice.schedule_of_provers
        [Eprover, Vampire, Zipperposition] 5)
    val _ = expect_equal "golden 24-slice rotation"
      [Vampire, Eprover, Zipperposition, Vampire, Eprover, Vampire,
       Zipperposition, Vampire, Vampire, Eprover, Zipperposition,
       Eprover, Vampire, Eprover, Vampire, Zipperposition, Vampire,
       Eprover, Zipperposition, Vampire, Eprover, Vampire, Eprover,
       Vampire]
      (hhSlice.schedule_of_provers
        [Eprover, Vampire, Zipperposition] 24)
    val _ = expect_equal "rotation filters and extends in requested order"
      [Eprover, Zipperposition, Eprover, Zipperposition, Eprover,
       Zipperposition, Eprover]
      (hhSlice.schedule_of_provers [Zipperposition, Eprover] 7)
    val defaults = slice_options [Eprover, Vampire, Zipperposition]
      (24 * 32) 32 30 "" NONE
    val default_schedule = hhSlice.mk_schedule defaults
    val _ = expect_equal "golden 24-slice Phase 3 schedule"
      expected_default (map (slice_summary o #2) default_schedule)
    val _ = expect_equal "frozen 16-slice Phase 2 schedule prefix"
      phase2_golden
      (List.take (map (slice_summary o #2) default_schedule, 16))
    val _ = expect_equal "Phase 1 eight-slice prefix is frozen verbatim"
      phase1 (List.take (map (slice_summary o #2) default_schedule, 8))
    val gate30 = slice_options [Eprover, Vampire, Zipperposition]
      8 8 30 "knn" NONE
    val gate10 = slice_options [Eprover, Vampire, Zipperposition]
      8 8 10 "knn" NONE
    val gate30_schedule = hhSlice.mk_schedule gate30
    val gate10_schedule = hhSlice.mk_schedule gate10
    val expected_gate = List.take (phase1, 8)
    val _ = expect_equal "gate freezes the first eight schedule slices"
      expected_gate (map (slice_summary o #2) gate30_schedule)
    val _ = expect_equal "S30 and S10 use the same frozen schedule"
      (schedule_summary gate30_schedule) (schedule_summary gate10_schedule)
    fun close expected actual = Real.abs (expected - actual) < 0.000001
    val _ = expect "eight-core gate gives every S30 slice 30 seconds"
      (List.all (fn (_, slice) =>
         close 30.0 (hhSlice.slice_budget 8 gate30 slice)) gate30_schedule)
    val _ = expect "eight-core gate gives every S10 slice 10 seconds"
      (List.all (fn (_, slice) =>
         close 10.0 (hhSlice.slice_budget 8 gate10 slice)) gate10_schedule)
    val anchors = gate30_schedule
    fun anchor_command_equal (config, slice) =
      let
        val baseline : hhProver.run_request =
          {timeout = 30, problem = "anchor.p", extra = [],
           debug_dir = NONE}
        val scheduled : hhProver.run_request =
          {timeout = 30, problem = "anchor.p",
           extra = #extra_opts slice, debug_dir = NONE}
      in
        #mk_command config "anchor-prover" baseline =
        #mk_command config "anchor-prover" scheduled
      end
    val _ = expect "gate anchors are command-equivalent to one-shot B"
      (List.all anchor_command_equal anchors)
    val small = hhSlice.mk_schedule
      (slice_options [Eprover, Vampire, Zipperposition] 5 2 30 "knn"
        NONE)
    val _ = expect_equal "small schedule follows the golden rotation"
      (List.take (schedule_summary default_schedule, 5))
      (schedule_summary small)
    val subset = hhSlice.mk_schedule
      (slice_options [Zipperposition, Eprover] 7 4 30 "knn" NONE)
    val _ = expect_equal "prover subset consumes each table head-first"
      [("e", 128, "knn", []),
       ("zipperposition", 128, "knn", []),
       ("e", 512, "knn", []),
       ("zipperposition", 512, "knn", []),
       ("e", 128, "knn", []),
       ("zipperposition", 128, "knn", []),
       ("e", 512, "knn", [])]
      (schedule_summary subset)
    val overridden = hhSlice.mk_schedule
      (slice_options [Eprover] 20 2 30 "none" (SOME 40))
    val _ = expect_equal "fact and filter overrides precede deduplication"
      [("e", 40, "none", []),
       ("e", 40, "none", []),
       ("e", 40, "none", []),
       ("e", 40, "none", [])]
      (schedule_summary overridden)
    val filter_override = hhSlice.mk_schedule
      (slice_options [Eprover, Vampire, Zipperposition] 24 24 30
        "none" NONE)
    val _ = expect "set filter overrides every per-slice table value"
      (not (null filter_override) andalso
       List.all (fn (_, slice) => #filter slice = "none") filter_override)
    val exhausted = hhSlice.mk_schedule
      (slice_options [Eprover, Vampire, Zipperposition] 100 8 30 ""
        NONE)
    val _ = expect "rotation exhaustion stops at twenty-four slices"
      (length exhausted = 24)
    val _ = expect "Z3 remains outside the slice scheduler"
      (null (hhSlice.mk_schedule
        (slice_options [Z3] 100 8 30 "knn" NONE)))
    val first_slice = #2 (hd default_schedule)
    val large_slice : hhProver.slice =
      {prover = #prover first_slice, format = #format first_slice,
       type_enc = #type_enc first_slice, lam_trans = #lam_trans first_slice,
       nfacts = #nfacts first_slice, filter = #filter first_slice,
       extra_opts = #extra_opts first_slice, slice_size = 3}
    val _ = expect "budget uses full timeout when slices fit on cores"
      (close 30.0 (hhSlice.slice_budget (length default_schedule) defaults
        first_slice))
    val budget_options = slice_options [Eprover] 999 32 30 "knn" NONE
    val _ = expect "budget arithmetic uses ceiling batches"
      (close 15.0 (hhSlice.slice_budget 33 budget_options first_slice) andalso
       close 15.0 (hhSlice.slice_budget 64 budget_options first_slice) andalso
       close 10.0 (hhSlice.slice_budget 65 budget_options first_slice) andalso
       close 30.0 (hhSlice.slice_budget 65 budget_options large_slice) andalso
       close 0.0 (hhSlice.slice_budget 0 budget_options first_slice))
    fun slice_of format type_enc lam_trans : hhProver.slice =
      {prover = Eprover, format = format, type_enc = type_enc,
       lam_trans = lam_trans, nfacts = 0, filter = "none", extra_opts = [],
       slice_size = 1}
    val triple_options : hhConfig.hh_options =
      {timeout = 30, max_proofs = 4, provers = [Eprover], slices = 1, cores = 1,
      export_workers = 1,
       filter = "knn", max_facts = NONE, format = "tf0",
       type_enc = "mono_native", lam_trans = "lifting", mono_iters = 3,
       mono_instances = NONE, minimize = true, preplay_timeout = 1.0,
       minimize_timeout = 1.0, cache = false, cache_dir = "",
       cache_max_entries = 100000, debug_dir = NONE,
       preplay_drop_one = false, verbose = false}
    val triple_schedule = hhSlice.mk_schedule triple_options
    val _ = expect "slice construction accepts a supported full triple"
      (case triple_schedule of
           [(_, slice)] => #format slice = "tf0" andalso
                         #type_enc slice = "mono_native" andalso
                         #lam_trans slice = "lifting"
         | _ => false)
    val _ = expect "slice encodings dispatch on the parsed type encoding"
      (hhSlice.encoding_of (slice_of "fof" "" "") = hhSlice.Legacy andalso
       (case hhSlice.encoding_of (slice_of "fof" "mono_guards" "combs") of
            hhSlice.Generated {lam_trans, ...} => lam_trans = hhLamTrans.Combs
          | hhSlice.Legacy => false) andalso
       ((ignore (hhSlice.encoding_of (slice_of "fof" "" "lifting")); false)
        handle Fail _ => true))
    fun invalid_triple format type_enc lam_trans =
      let
        val options : hhConfig.hh_options =
          {timeout = 30, max_proofs = 4, provers = [Eprover], slices = 1,
           cores = 1,
           export_workers = 1,
           filter = "knn", max_facts = NONE, format = format,
           type_enc = type_enc, lam_trans = lam_trans, mono_iters = 3,
           mono_instances = NONE, minimize = true, preplay_timeout = 1.0,
           minimize_timeout = 1.0, cache = false, cache_dir = "",
           cache_max_entries = 100000, debug_dir = NONE,
           preplay_drop_one = false, verbose = false}
      in
        ((ignore (hhSlice.mk_schedule options); false) handle Fail _ => true)
      end
    val _ = expect "slice construction rejects incoherent triples"
      (invalid_triple "tf0" "" "lifting" andalso
       invalid_triple "th1" "mono_native_higher" "keep_lams" andalso
       invalid_triple "tf0" "mono_native" "")
    fun filter_test_config filter : hhProver.prover_config =
      let
        val slice : hhProver.slice =
          {prover = Z3, format = "fof", type_enc = "", lam_trans = "",
           nfacts = 1, filter = filter, extra_opts = [], slice_size = 1}
      in
        {name = "selftest-filter", exec_names = [], env_var = "",
         version_args = [], parse_version = fn _ => NONE,
         tested_versions = [], supported_formats = ["fof"],
         mk_command = fn executable => fn _ => (executable, []),
         parse_output = fn _ => (hhProver.SzsUnknown "selftest", NONE),
         mono_instances = 100, slices = [slice], legacy = true}
      end
    fun rejects_filter filter =
      hhProver.with_override Z3 (filter_test_config filter) (fn () =>
        (ignore (hhSlice.mk_schedule
          (slice_options [Z3] 1 1 30 "" NONE)); false)
        handle Fail _ => true)
    val _ = expect "slice construction validates the filter vocabulary"
      (List.all rejects_filter ["", "not-a-filter"])
  in
    ()
  end

fun cache_options directory maximum enabled : hhConfig.hh_options =
  {timeout = 30, max_proofs = 4, provers = [Eprover], slices = 1,
   cores = 1,
   export_workers = 1,
   filter = "knn", max_facts = NONE,
   format = "", type_enc = "", lam_trans = "", mono_iters = 3,
   mono_instances = NONE, minimize = true,
   preplay_timeout = 1.0, minimize_timeout = 1.0, cache = enabled,
   cache_dir = directory, cache_max_entries = maximum, debug_dir = NONE,
   preplay_drop_one = false, verbose = false}

fun test_hhCache () =
  let
    val root = OS.FileSys.tmpName ()
    val _ = remove_tree root
    val _ = mkdir root
    val moved = join root "moved"
    val cache = join root "cache"
    val lru_cache = join root "lru"
    val _ = mkdir moved
    val problem1 = join root "problem.p"
    val problem2 = join moved "renamed.p"
    val problem3 = join root "changed.p"
    val contents = "fof(cache_fixture, conjecture, $true).\n"
    val _ = write_file problem1 contents
    val _ = write_file problem2 contents
    val _ = write_file problem3 (contents ^ "% changed\n")
    val first : hhCache.key_parts =
      {prover = "e", version = SOME "3.2.5",
       argv = ["--cpu-limit=10", problem1], problem = problem1}
    val relocated : hhCache.key_parts =
      {prover = "e", version = SOME "3.2.5",
       argv = ["--cpu-limit=10", problem2], problem = problem2}
    val longer : hhCache.key_parts =
      {prover = "e", version = SOME "3.2.5",
       argv = ["--cpu-limit=20", problem1], problem = problem1}
    val upgraded : hhCache.key_parts =
      {prover = "e", version = SOME "3.3",
       argv = ["--cpu-limit=10", problem1], problem = problem1}
    val changed : hhCache.key_parts =
      {prover = "e", version = SOME "3.2.5",
       argv = ["--cpu-limit=10", problem3], problem = problem3}
    val first_key = hhCache.key_of first
    val _ = expect "cache key is a SHA-1 digest"
      (String.size first_key = 40 andalso
       List.all Char.isHexDigit (String.explode first_key))
    val _ = expect "cache key ignores the problem path"
      (first_key = hhCache.key_of relocated)
    val _ = expect "cache key includes timeout and options"
      (first_key <> hhCache.key_of longer)
    val _ = expect "cache key includes the probed prover version"
      (first_key <> hhCache.key_of upgraded)
    val _ = expect "cache key includes problem contents"
      (first_key <> hhCache.key_of changed)
    val boundary1 : hhCache.key_parts =
      {prover = "ab", version = NONE, argv = ["c", problem1],
       problem = problem1}
    val boundary2 : hhCache.key_parts =
      {prover = "a", version = NONE, argv = ["bc", problem1],
       problem = problem1}
    val _ = expect "cache key fields have unambiguous boundaries"
      (hhCache.key_of boundary1 <> hhCache.key_of boundary2)
    val options = cache_options cache 100 true
    val stored : hhProver.run_result =
      {szs = hhProver.SzsTheorem, used_axioms = SOME ["a", "b"],
       time = 1.25, version = SOME "3.2.5", output_file = "ignored.out"}
    val _ = hhCache.store options (hhCache.key_of first) stored
    val round_trip = hhCache.lookup options (hhCache.key_of relocated)
    val _ = expect "cache store and relocated lookup round-trip"
      (case round_trip of
           SOME result =>
             #szs result = hhProver.SzsTheorem andalso
             #used_axioms result = SOME ["a", "b"] andalso
             Real.abs (#time result - 1.25) < 0.000001 andalso
             #version result = SOME "3.2.5" andalso
             #output_file result = ""
         | NONE => false)
    val _ = expect "a longer timeout is a cache miss"
      (not (Option.isSome
        (hhCache.lookup options (hhCache.key_of longer))))
    val timeout_result : hhProver.run_result =
      {szs = hhProver.SzsTimeout, used_axioms = NONE, time = 10.0,
       version = SOME "3.2.5", output_file = "timeout.out"}
    val _ = hhCache.store options (hhCache.key_of longer) timeout_result
    val _ = expect "timeout results are cached"
      (case hhCache.lookup options (hhCache.key_of longer) of
           SOME result => #szs result = hhProver.SzsTimeout
         | NONE => false)
    val corrupt : hhCache.key_parts =
      {prover = "e", version = NONE, argv = ["--corrupt", problem1],
       problem = problem1}
    val corrupt_path = join cache (hhCache.key_of corrupt)
    val _ = write_file corrupt_path "this is not JSON"
    val _ = expect "corrupt cache entries are misses"
      (not (Option.isSome
        (hhCache.lookup options (hhCache.key_of corrupt))))
    val _ = expect "corrupt cache entries are deleted"
      (not (OS.FileSys.access (corrupt_path, [])))
      handle OS.SysErr _ => OK ()
    val disabled : hhCache.key_parts =
      {prover = "e", version = NONE, argv = ["--disabled", problem1],
       problem = problem1}
    val _ = hhCache.store (cache_options cache 100 false)
      (hhCache.key_of disabled) stored
    val _ = expect "disabled cache does not store entries"
      (not (OS.FileSys.access (join cache (hhCache.key_of disabled), [])))
      handle OS.SysErr _ => OK ()
    fun lru_parts number : hhCache.key_parts =
      {prover = "e", version = SOME "3.2.5",
       argv = ["--slice=" ^ Int.toString number, problem1],
       problem = problem1}
    val lru_parts_list = List.tabulate (6, lru_parts)
    val lru_options = cache_options lru_cache 5 true
    val _ = List.app
      (fn parts => hhCache.store lru_options (hhCache.key_of parts) stored)
      lru_parts_list
    fun path_of parts = join lru_cache (hhCache.key_of parts)
    fun set_times ([], _) = ()
      | set_times (parts :: rest, seconds) =
          (OS.FileSys.setTime
             (path_of parts, SOME (Time.fromSeconds
               (LargeInt.fromInt seconds)));
           set_times (rest, seconds + 10))
    val _ = set_times (lru_parts_list, 10)
    val oldest = hd lru_parts_list
    val before_touch = OS.FileSys.modTime (path_of oldest)
    val _ = ignore (hhCache.lookup lru_options (hhCache.key_of oldest))
    val after_touch = OS.FileSys.modTime (path_of oldest)
    val _ = expect "cache lookup refreshes the LRU mtime"
      (Time.compare (after_touch, before_touch) = GREATER)
    val _ = hhCache.prune lru_options
    fun exists parts = OS.FileSys.access (path_of parts, [])
      handle OS.SysErr _ => false
    val _ = expect "cache prune removes oldest entries after a touch"
      (exists (List.nth (lru_parts_list, 0)) andalso
       not (exists (List.nth (lru_parts_list, 1))) andalso
       not (exists (List.nth (lru_parts_list, 2))) andalso
       List.all exists (List.drop (lru_parts_list, 3)))
    val _ = expect "cache prune enforces the ninety-percent bound"
      (length (hhConfig.directory_names lru_cache) = 4)
    val _ = remove_tree root
  in
    ()
  end

fun contains needle haystack =
  String.isSubstring needle haystack

fun hh_error call =
  ((call (); NONE)
   handle Feedback.HOL_ERR error => SOME (Feedback.message_of error))

fun test_holyHammer_validation () =
  let
    val unknown = "not-a-holyhammer-prover"
    val _ = expect "prover option rejects unknown prover names"
      (option_error [unknown, "prover names: e, vampire"]
        (fn () => hhConfig.hh_set ("provers", unknown)))
  in
    case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
        NONE => ()
      | SOME _ =>
          let
            val output = OS.FileSys.tmpName ()
            val message = smlRedirect.hide_in_file output
              (fn () => hh_error (fn () =>
                ignore (holyHammer.hh_pb "" [Zipperposition] []
                  ([], boolSyntax.T)))) ()
            val printed = String.concat (read_lines output)
            val _ = OS.FileSys.remove output
          in
            expect "no-prover path prints downloader hint"
              (contains "tools/download-provers" printed andalso
               case message of
                   SOME text => contains "tools/download-provers" text
                 | NONE => false)
          end
  end

fun fake_config name exec_name args parser : hhProver.prover_config =
  {name = name, exec_names = [exec_name], env_var = "",
   version_args = ["--version"], parse_version = fn _ => SOME "test",
   tested_versions = ["test"], supported_formats = ["fof"],
   mk_command = fn executable => fn _ => (executable, args),
   parse_output = parser, mono_instances = 100,
   slices = [],
   legacy = false}

fun wait_until deadline predicate =
  if predicate () then true
  else if Time.> (Time.now (), deadline) then false
  else
    (OS.Process.sleep (Time.fromMilliseconds 20);
     wait_until deadline predicate)

fun pid_from_output output =
  case String.tokens Char.isSpace output of
      word :: _ =>
        (case Int.fromString word of
             SOME number =>
               Posix.Process.wordToPid (SysWord.fromInt number)
           | NONE => raise Fail "fixture printed a non-numeric pid")
    | [] => raise Fail "fixture did not print its child pid"

fun process_is_gone pid =
  let
    val signal_zero = Posix.Signal.fromWord 0w0
  in
    ((Posix.Process.kill (Posix.Process.K_PROC pid, signal_zero); false)
     handle OS.SysErr (_, SOME error) => OS.errorName error = "ESRCH")
  end

fun test_runner_load parser =
  let
    val workers = 24
    val config = fake_config "runner-load" "/bin/echo"
      ["% SZS status Theorem"] parser
    val request : hhProver.run_request =
      {timeout = 2, problem = "unused", extra = [],
       debug_dir = NONE}
    val _ = ignore (hhProver.probe config)
    val _ = hhProver.reset_spawn_count ()
    val result_mutex = Mutex.mutex ()
    val finished = ref 0
    val passed = ref 0
    fun note success =
      let
        val _ = Mutex.lock result_mutex
        val _ = finished := !finished + 1
        val _ = if success then passed := !passed + 1 else ()
      in
        Mutex.unlock result_mutex
      end
    fun worker () =
      let
        val running = hhProver.run_async config request
        val result = #wait running ()
      in
        note (#szs result = hhProver.SzsTheorem)
      end
      handle _ => note false
    val _ = List.tabulate (workers, fn _ => Thread.fork (worker, []))
    fun all_finished () =
      let
        val _ = Mutex.lock result_mutex
        val done = !finished = workers
        val _ = Mutex.unlock result_mutex
      in
        done
      end
    val completed = wait_until
      (Time.+ (Time.now (), Time.fromSeconds 15)) all_finished
    val _ = Mutex.lock result_mutex
    val successes = !passed
    val _ = Mutex.unlock result_mutex
    val _ = expect "runner concurrent load completes"
      (completed andalso successes = workers)
    val _ = expect "runner spawn counter counts concurrent forks"
      (hhProver.spawn_count () = workers)
  in
    ()
  end

fun test_runner () =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      SOME _ => ()
    | NONE =>
  let
    val e = prover Eprover
    val good = fake_config "runner-good" "/bin/echo"
      ["% SZS status Theorem"] (#parse_output e)
    val debug_dir = OS.FileSys.tmpName ()
    val _ = remove_tree debug_dir
    val good_request : hhProver.run_request =
      {timeout = 1, problem = "unused", extra = [],
       debug_dir = SOME debug_dir}
    val good_result = hhProver.run good good_request
    val _ = expect "runner parses stdout"
      (#szs good_result = hhProver.SzsTheorem)
    val _ = expect "runner saves debug output"
      (OS.FileSys.access (#output_file good_result, [OS.FileSys.A_READ]))
    val _ = remove_tree debug_dir
    val timeout = fake_config "runner-timeout" "/bin/sleep" ["30"]
      (#parse_output e)
    val timeout_request : hhProver.run_request =
      {timeout = 0, problem = "unused", extra = [],
       debug_dir = NONE}
    val timeout_result = hhProver.run timeout timeout_request
    val _ = expect "runner watchdog timeout"
      (#szs timeout_result = hhProver.SzsTimeout orelse
       #szs timeout_result = hhProver.SzsResourceOut)
    val killed = fake_config "runner-killed" "/bin/sleep" ["30"]
      (#parse_output e)
    val kill_request : hhProver.run_request =
      {timeout = 30, problem = "unused", extra = [],
       debug_dir = NONE}
    val running_sleep = hhProver.run_async killed kill_request
    val _ = #kill running_sleep ()
    val _ = #kill running_sleep ()
    val killed_result = #wait running_sleep ()
    val killed_result_again = #wait running_sleep ()
    val _ = expect "runner kill returns before child exit"
      (#szs killed_result = hhProver.SzsTimeout andalso
       #szs killed_result_again = hhProver.SzsTimeout andalso
       Real.== (#time killed_result, #time killed_result_again) andalso
       #time killed_result < 5.0)
    val fixture_dir = "test-data"
    val printer_path = join fixture_dir "runner-print-e.sh"
    val printer = fake_config "runner-printer" printer_path []
      (#parse_output e)
    val printer_dir = OS.FileSys.tmpName ()
    val _ = remove_tree printer_dir
    val printer_request : hhProver.run_request =
      {timeout = 2, problem = "unused", extra = [],
       debug_dir = SOME printer_dir}
    val printer_result = hhProver.run printer printer_request
    val printed = String.concat (read_lines (#output_file printer_result))
    val recorded = String.concat
      (read_lines (join fixture_dir "e-theorem-chatter.out"))
    val _ = expect "runner captures stdout intact"
      (#szs printer_result = hhProver.SzsTheorem andalso
       printed = recorded)
    val _ = remove_tree printer_dir
    val forking_path = join fixture_dir "runner-forking-sleeper.sh"
    val forking = fake_config "runner-forking" forking_path []
      (#parse_output e)
    val forking_dir = OS.FileSys.tmpName ()
    val _ = remove_tree forking_dir
    val forking_request : hhProver.run_request =
      {timeout = 30, problem = "unused", extra = [],
       debug_dir = SOME forking_dir}
    val running_fork = hhProver.run_async forking forking_request
    val _ = OS.Process.sleep (Time.fromMilliseconds 200)
    val _ = #kill running_fork ()
    val forking_result = #wait running_fork ()
    val grandchild = pid_from_output
      (String.concat (read_lines (#output_file forking_result)))
    val grandchild_gone = wait_until
      (Time.+ (Time.now (), Time.fromSeconds 5))
      (fn () => process_is_gone grandchild)
    val _ = expect "runner group kill reaps grandchild" grandchild_gone
    val _ = remove_tree forking_dir
    val exec_failure : hhProver.prover_config =
      {name = "runner-exec-failure", exec_names = ["/bin/true"],
       env_var = "", version_args = [], parse_version = fn _ => SOME "test",
       tested_versions = ["test"], supported_formats = ["fof"],
       mk_command = fn _ => fn _ =>
         ("/definitely/missing/holyhammer-prover", []),
       parse_output = #parse_output e,
       mono_instances = 100, slices = [], legacy = false}
    val exec_result = hhProver.run exec_failure timeout_request
    val _ = expect "runner exec failure returns RunFailure"
      (case #szs exec_result of hhProver.RunFailure _ => true | _ => false)
    val missing : hhProver.prover_config =
      {name = "runner-missing", exec_names = ["missing-hh-prover"],
       env_var = "", version_args = [], parse_version = fn _ => NONE,
       tested_versions = [], supported_formats = ["fof"],
       mk_command = fn executable => fn _ => (executable, []),
       parse_output = #parse_output e,
       mono_instances = 100, slices = [], legacy = false}
    val missing_result = hhProver.run missing timeout_request
    val _ = expect "missing prover names downloader"
      (case #szs missing_result of
           hhProver.RunFailure message =>
             contains "tools/download-provers" message
         | _ => false)
    val _ = test_runner_load (#parse_output e)
  in
    ()
  end

fun write_tiny_problem () =
  let
    val path = OS.FileSys.tmpName ()
    val _ = write_file path
      "fof(thm_2Ekeep__name, axiom, p).\nfof(conjecture, conjecture, p).\n"
  in
    path
  end

fun test_installed_prover problem config =
  case hhProver.probe config of
      NONE => (tprint ("runner smoke " ^ #name config ^ " (skipped: absent)");
               OK ())
    | SOME _ =>
        let
          val request : hhProver.run_request =
            {timeout = 5, problem = problem, extra = [],
             debug_dir = NONE}
          val result = hhProver.run config request
        in
          expect ("runner smoke " ^ #name config)
            (#szs result = hhProver.SzsTheorem)
        end

fun test_installed_provers () =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      SOME _ => ()
    | NONE =>
        let
          val problem = write_tiny_problem ()
          val _ = List.app (test_installed_prover problem)
            (map prover [Eprover, Vampire, Zipperposition, Z3])
          val _ = OS.FileSys.remove problem handle OS.SysErr _ => ()
        in
          ()
        end

fun same_real left right = Real.== (left, right)

fun same_real_option NONE NONE = true
  | same_real_option (SOME left) (SOME right) = same_real left right
  | same_real_option _ _ = false

val same_slice = hhProver.same_slice

fun same_journal_slice (expected : hhEval.journal_slice)
    (actual : hhEval.journal_slice) =
  same_slice (#slice expected) (#slice actual) andalso
  #szs expected = #szs actual andalso
  same_real (#time expected) (#time actual) andalso
  #cached expected = #cached actual

fun same_journal_entry (expected : hhEval.journal_entry)
    (actual : hhEval.journal_entry) =
  #run expected = #run actual andalso #thy expected = #thy actual andalso
  #thm expected = #thm actual andalso
  #goal_id expected = #goal_id actual andalso
  #cond expected = #cond actual andalso
  hhEval.string_of_regime (#regime expected) =
    hhEval.string_of_regime (#regime actual) andalso
  hhEval.string_of_selector (#selector expected) =
    hhEval.string_of_selector (#selector actual) andalso
  #engine expected = #engine actual andalso
  #ho expected = #ho actual andalso #fresh expected = #fresh actual andalso
  #prover expected = #prover actual andalso
  #prover_version expected = #prover_version actual andalso
  #nfacts expected = #nfacts actual andalso
  #timeout expected = #timeout actual andalso
  #szs expected = #szs actual andalso
  same_real (#t_prover expected) (#t_prover actual) andalso
  #axioms_used expected = #axioms_used actual andalso
  #recon_ok expected = #recon_ok actual andalso
  #recon_method expected = #recon_method actual andalso
  same_real_option (#t_recon expected) (#t_recon actual) andalso
  #stac expected = #stac actual andalso #error expected = #error actual andalso
  #stop expected = #stop actual andalso
  same_real_option (#t_total expected) (#t_total actual) andalso
  (case (#winner expected, #winner actual) of
       (NONE, NONE) => true
     | (SOME left, SOME right) => same_slice left right
     | _ => false) andalso
  ListPair.allEq (fn (left, right) => same_journal_slice left right)
    (#slices expected, #slices actual)

fun test_hhEval root =
  let
    val num_ty = Type.mk_type ("num", [])
    val num_fun_ty = Type.mk_type ("fun", [num_ty, num_ty])
    val bool_predicate_ty = Type.mk_type ("fun", [Type.bool, Type.bool])
    val x = Term.mk_var ("x", num_ty)
    val f = Term.mk_var ("f", num_fun_ty)
    val bool_predicate = Term.mk_var ("P", bool_predicate_ty)
    val residual_lambda : Term.term = ``(\x : num. x) = (\x. x)``
    val applied_bound_function : Term.term = ``!f : num -> num. f 0 = f 0``
    val connective_in_term = Term.mk_comb (bool_predicate, ``T /\ T``)
    val quantifier_in_term = Term.mk_comb (bool_predicate, ``!x : num. x = x``)
    val plain_first_order : Term.term = ``(1 : num) = 1``
    val binder_only : Term.term = ``!x : num. x = x``
    val beta_redex = Term.mk_comb (Term.mk_abs (x, x), ``0 : num``)
    val eta_redex = Term.mk_abs (x, Term.mk_comb (f, x))
    val _ = expect "HO classifier hand-labelled fixtures"
      (List.all (fn (tm, expected) => hhEval.is_higher_order_goal tm = expected)
       [(residual_lambda, true), (applied_bound_function, true),
        (connective_in_term, true), (quantifier_in_term, true),
        (plain_first_order, false), (binder_only, false)])
    val _ = expect "HO classifier beta-eta invariant"
      (hhEval.is_higher_order_goal beta_redex =
         hhEval.is_higher_order_goal ``0 : num`` andalso
       hhEval.is_higher_order_goal eta_redex =
         hhEval.is_higher_order_goal f)
    val fresh_statement : Term.term = ``([] : num list) = []``
    val seen_statement : Term.term = ``(0 : num) = 0``
    val fresh_beta = Term.mk_comb
      (Term.mk_abs (x, fresh_statement), ``0 : num``)
    val _ = expect "fresh-symbol classifier fixtures"
      (hhEval.is_fresh_goal "list" fresh_statement andalso
       not (hhEval.is_fresh_goal "list" seen_statement) andalso
       not (hhEval.is_fresh_goal "fixture" fresh_statement))
    val _ = expect "fresh-symbol classifier beta invariant"
      (hhEval.is_fresh_goal "list" fresh_beta =
       hhEval.is_fresh_goal "list" fresh_statement)
    val holdir = join root "holdir"
    val sigobj = join holdir "sigobj"
    val src = join holdir "src"
    val _ = mkdirs sigobj
    val _ = mkdirs (join (join (join src "one") ".hol") "objs")
    val _ = mkdirs (join (join (join src "two") ".hol") "objs")
    val _ = write_file (join sigobj "SRCFILES")
      (join src "one/listTheory" ^ "\n" ^
       join src "two/arithmeticTheory" ^ "\n")
    val _ = write_file (join (join (join (join src "one") ".hol") "objs")
      "listTheory.dat") ""
    val _ = write_file (join (join (join (join src "two") ".hol") "objs")
      "arithmeticTheory.dat") ""
    val _ = write_file (join (join (join (join src "two") ".hol") "objs")
      "missingTheory.dat") ""
    val coverage = hhEval.stdlib_coverage ()
    val _ = expect_equal "SRCFILES corpus parser"
      ["arithmetic", "list"] (#srcfiles coverage)
    val _ = expect_equal "coverage check records discrepancy" ["missing"]
      (#added_from_dat coverage)
    val _ = expect_equal "stdlib corpus explicitly adds discrepancy"
      ["arithmetic", "list", "missing"] (hhEval.stdlib_theories ())
    val expdir = join root "hheval"
    val _ = remove_tree expdir
    val journal = hhEval.journal_path expdir "list"
    val null_entry : hhEval.journal_entry =
      {run = "fixture", thy = "list", thm = "nil", goal_id = "list.nil",
       cond = "deps-e", regime = hhEval.Bushy, selector = hhEval.Deps,
       engine = SOME (hhEval.Prover Eprover), ho = false, fresh = false,
       prover = SOME Eprover,
       prover_version = NONE,
       nfacts = 0, timeout = 5,
       szs = hhEval.BrokenDeps, t_prover = 0.0, axioms_used = NONE,
       recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = NONE, stop = NONE, t_total = NONE, winner = NONE, slices = []}
    val full_entry : hhEval.journal_entry =
      {run = "fixture", thy = "list", thm = "cons", goal_id = "list.cons",
       cond = "knn-e", regime = hhEval.Chainy, selector = hhEval.Knn 128,
       engine = SOME (hhEval.Prover Eprover), ho = true, fresh = true,
       prover = SOME Eprover,
       prover_version = SOME "3.2.5", nfacts = 128,
       timeout = 10, szs = hhEval.Szs hhProver.SzsTheorem,
       t_prover = 1.25,
       axioms_used = SOME ["list.nil", "arithmetic.add"], recon_ok = SOME true,
       recon_method = SOME "metis", t_recon = SOME 0.5,
       stac = SOME "metis_tac [list_nil]", error = SOME "fixture",
       stop = NONE, t_total = NONE, winner = NONE, slices = []}
    val _ = expect "journal null-field round trip"
      (same_journal_entry null_entry
       (hhEval.parse_journal_line (hhEval.encode_journal_line null_entry)))
    val _ = expect "journal populated-field round trip"
      (same_journal_entry full_entry
       (hhEval.parse_journal_line (hhEval.encode_journal_line full_entry)))
    val load_entry : hhEval.journal_entry =
      {run = "fixture", thy = "list", thm = "__load__",
       goal_id = "list.__load__", cond = "__load__", regime = hhEval.Bushy,
       selector = hhEval.Deps, engine = NONE, ho = false, fresh = false,
       prover = NONE, prover_version = NONE, nfacts = 0, timeout = 0,
       szs = hhEval.LoadFailure, t_prover = 0.0, axioms_used = NONE,
       recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = SOME "fixture", stop = NONE, t_total = NONE, winner = NONE,
       slices = []}
    val load_line = hhEval.encode_journal_line load_entry
    val _ = expect "theory-load entries round-trip without an engine"
      (same_journal_entry load_entry (hhEval.parse_journal_line load_line)
       andalso String.isSubstring "\"engine\":\"prover\"" load_line
       andalso String.isSubstring "\"prover\":\"\"" load_line)
    val _ = hhEval.append_journal journal null_entry
    val _ = hhEval.append_journal journal full_entry
    val entries = hhEval.read_journal journal
    val _ = expect "journal append flushes both lines"
      (length entries = 2 andalso same_journal_entry null_entry (hd entries))
    val complete = [("list.nil", "deps-e"), ("list.cons", "knn-e")]
    val _ = expect "resume complete journal"
      (hhEval.journal_complete journal complete)
    val corrupt = TextIO.openAppend journal
    val _ = TextIO.output (corrupt, "{interrupted-write")
    val _ = TextIO.closeOut corrupt
    val _ = expect "resume ignores a truncated final journal record"
      (hhEval.journal_complete journal complete andalso
       length (hhEval.read_journal journal) = 2)
    val partial = hhEval.journal_path expdir "partial"
    val _ = hhEval.append_journal partial null_entry
    val _ = expect "resume partial journal"
      (not (hhEval.journal_complete partial complete))
    val empty = hhEval.journal_path expdir "empty"
    val _ = expect "resume empty journal"
      (not (hhEval.journal_complete empty complete))
    val retry = hhEval.journal_path expdir "retry"
    val retry_entry : hhEval.journal_entry =
      {run = "fixture", thy = "list", thm = "nil", goal_id = "list.nil",
       cond = "deps-e", regime = hhEval.Bushy, selector = hhEval.Deps,
       engine = SOME (hhEval.Prover Eprover), ho = false, fresh = false,
       prover = SOME Eprover,
       prover_version = NONE, nfacts = 0, timeout = 5,
       szs = hhEval.EvalError, t_prover = 0.0, axioms_used = NONE,
       recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = SOME "transient harness failure", stop = NONE,
       t_total = NONE, winner = NONE, slices = []}
    val _ = hhEval.append_journal retry retry_entry
    val _ = expect "resume retries harness errors"
      (not (hhEval.cell_completed (hhEval.read_completed retry)
        ("list.nil", "deps-e")))
    val run_failure = hhEval.journal_path expdir "runfailure"
    val _ = hhEval.append_journal run_failure
      {run = #run retry_entry, thy = #thy retry_entry,
       thm = #thm retry_entry, goal_id = #goal_id retry_entry,
       cond = #cond retry_entry, regime = #regime retry_entry,
       selector = #selector retry_entry, engine = #engine retry_entry,
       ho = #ho retry_entry, fresh = #fresh retry_entry,
       prover = #prover retry_entry,
       prover_version = NONE, nfacts = 0, timeout = 5,
       szs = hhEval.Szs (hhProver.RunFailure ""), t_prover = 0.0,
       axioms_used = NONE,
       recon_ok = NONE, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = SOME "prover binary was missing", stop = NONE,
       t_total = NONE, winner = NONE, slices = []}
    val _ = expect "resume retries cells whose prover never ran"
      (not (hhEval.cell_completed (hhEval.read_completed run_failure)
        ("list.nil", "deps-e")))
    (* A resume appends past the torn record an interrupted worker left,
       so the malformed line ends up in the middle of the journal. *)
    val torn = hhEval.journal_path expdir "torn"
    val _ = hhEval.append_journal torn null_entry
    val torn_out = TextIO.openAppend torn
    val _ = TextIO.output (torn_out, "{interrupted-write\n")
    val _ = TextIO.closeOut torn_out
    val _ = hhEval.append_journal torn full_entry
    val _ = expect "resume ignores a truncated journal record mid-file"
      (hhEval.journal_complete torn complete andalso
       length (hhEval.read_journal torn) = 2)
    val condition : hhEval.condition =
      {cond_id = "knn-e", regime = hhEval.Chainy, selector = hhEval.Knn 128,
       engine = hhEval.Prover Eprover, timeout = 10, reconstruct = true}
    val parsed_condition =
      hhEval.parse_condition (hhEval.encode_condition condition)
    val _ = expect "condition serialization"
      (#cond_id parsed_condition = #cond_id condition andalso
       hhEval.string_of_regime (#regime parsed_condition) = "chainy" andalso
       hhEval.string_of_selector (#selector parsed_condition) = "knn128" andalso
       #engine parsed_condition = hhEval.Prover Eprover andalso
       #timeout parsed_condition = 10 andalso #reconstruct parsed_condition)
    val selectors =
      [(hhEval.Deps, "deps"), (hhEval.Knn 96, "knn96"),
       (hhEval.Mepo 96, "mepo96"), (hhEval.Mash 128, "mash128"),
       (hhEval.Mesh 256, "mesh256")]
    fun selector_round_trip (selector, spelling) =
      let
        val item : hhEval.condition =
          {cond_id = spelling, regime = hhEval.Chainy,
           selector = selector, engine = hhEval.Prover Eprover, timeout = 30,
           reconstruct = true}
        val parsed = hhEval.parse_condition (hhEval.encode_condition item)
      in
        hhEval.string_of_selector (#selector parsed) = spelling
      end
    val _ = expect "ensemble selector spelling round trips"
      (List.all selector_round_trip selectors)
    val malformed_selector =
      "{\"cond_id\":\"bad\",\"regime\":\"chainy\"," ^
      "\"selector\":\"mepo96x\",\"engine\":\"prover\"," ^
      "\"prover\":\"e\",\"timeout\":30,\"reconstruct\":true}"
    val _ = expect "selector grammar rejects suffixes and missing counts"
      ((ignore (hhEval.parse_condition malformed_selector);
        false) handle Fail _ => true)
    val sched_condition : hhEval.condition =
      {cond_id = "sched", regime = hhEval.Chainy,
       selector = hhEval.Knn 256,
       engine = hhEval.Sched
         {provers = [Eprover, Vampire], slices = 6, cores = 2,
          max_proofs = 3, export_workers = 2},
       timeout = 30, reconstruct = true}
    val parsed_sched_condition =
      hhEval.parse_condition (hhEval.encode_condition sched_condition)
    val _ = expect "Sched condition serialization"
      (#cond_id parsed_sched_condition = "sched" andalso
       #engine parsed_sched_condition = #engine sched_condition andalso
       #timeout parsed_sched_condition = 30 andalso
       #reconstruct parsed_sched_condition)
    val legacy_sched_condition =
      "{\"cond_id\":\"legacy\",\"regime\":\"chainy\"," ^
      "\"selector\":\"knn256\",\"engine\":\"sched\"," ^
      "\"provers\":[\"e\",\"vampire\"],\"slices\":6,\"cores\":2," ^
      "\"max_proofs\":3,\"timeout\":30,\"reconstruct\":true}"
    val _ = expect "Sched condition without export_workers gets the default"
      (#engine (hhEval.parse_condition legacy_sched_condition) =
         hhEval.Sched
           {provers = [Eprover, Vampire], slices = 6, cores = 2,
            max_proofs = 3,
            export_workers = hhConfig.default_export_workers})
    val perslice_condition : hhEval.condition =
      {cond_id = "perslice", regime = hhEval.Chainy,
       selector = hhEval.PerSlice, engine = #engine sched_condition,
       timeout = 30, reconstruct = true}
    val parsed_perslice =
      hhEval.parse_condition (hhEval.encode_condition perslice_condition)
    val _ = expect "PerSlice Sched condition serialization"
      (hhEval.string_of_selector (#selector parsed_perslice) =
         "perslice" andalso
       #engine parsed_perslice = #engine sched_condition)
    val invalid_perslice : hhEval.condition =
      {cond_id = "invalid-perslice", regime = hhEval.Chainy,
       selector = hhEval.PerSlice, engine = hhEval.Prover Eprover, timeout = 30,
       reconstruct = true}
    val _ = expect "PerSlice is rejected for non-Sched engines"
      ((hhEval.validate_condition invalid_perslice; false)
       handle Fail message => String.isSubstring "perslice" message)
    val invalid_sched : hhEval.condition =
      {cond_id = "invalid-sched", regime = hhEval.Bushy,
       selector = hhEval.Deps,
       engine = hhEval.Sched
         {provers = [Eprover], slices = 1, cores = 1, max_proofs = 1,
          export_workers = 1},
       timeout = 5, reconstruct = false}
    val _ = expect "Sched condition requires reconstruction"
      ((hhEval.validate_condition invalid_sched; false)
       handle Fail message =>
         String.isSubstring "Sched" message andalso
         String.isSubstring "reconstruct must be true" message)
    val schedule_slice : hhEval.journal_slice =
      {slice =
         {prover = Eprover, format = "fof", type_enc = "",
          lam_trans = "", nfacts = 256, filter = "mepo",
          extra_opts = ["--auto"], slice_size = 15},
       szs = hhProver.SzsTheorem, time = 1.75, cached = true}
    val competing_schedule_slice : hhEval.journal_slice =
      {slice =
         {prover = Eprover, format = "tx0-", type_enc = "mono_native_fool",
          lam_trans = "lifting", nfacts = 256, filter = "mepo",
          extra_opts = ["--auto"], slice_size = 15},
       szs = hhProver.SzsTheorem, time = 1.5, cached = false}
    val sched_entry : hhEval.journal_entry =
      {run = "fixture", thy = "list", thm = "scheduled",
       goal_id = "list.scheduled", cond = "sched",
       regime = hhEval.Chainy, selector = hhEval.Knn 256,
       engine = SOME (#engine sched_condition), ho = true, fresh = true,
       prover = SOME Eprover,
       prover_version = SOME "3.2.5", nfacts = 256, timeout = 30,
       szs = hhEval.Szs hhProver.SzsTheorem, t_prover = 1.75,
       axioms_used = SOME ["list.one"], recon_ok = SOME true,
       recon_method = SOME "metis", t_recon = SOME 0.25,
       stac = SOME "metis_tac [list_one]", error = NONE,
       stop = SOME "MaxProofs", t_total = SOME 2.0,
       winner = SOME (#slice schedule_slice),
       slices = [competing_schedule_slice, schedule_slice]}
    val sched_line = hhEval.encode_journal_line sched_entry
    val _ = expect "Sched journal round trip"
      (same_journal_entry sched_entry (hhEval.parse_journal_line sched_line))
    val sched_json = JSONParser.parseFile
      (let
         val path = join expdir "sched-line.json"
         val _ = write_file path sched_line
       in
         path
       end)
    val _ = expect
      "Sched journal emits engine, HO, fresh, and exact winner fields"
      (JSONUtil.asString (JSONUtil.lookupField sched_json "engine") =
         "sched" andalso
       JSONUtil.asBool (JSONUtil.lookupField sched_json "ho") andalso
       JSONUtil.asBool (JSONUtil.lookupField sched_json "fresh") andalso
       JSONUtil.asString (JSONUtil.lookupField
         (JSONUtil.lookupField sched_json "winner") "format") = "fof" andalso
       JSONUtil.asString (JSONUtil.lookupField
         (hd (JSONUtil.arrayMap (fn item => item)
           (JSONUtil.lookupField sched_json "slices"))) "szs") = "Theorem")
    (* The pre-v4 prover-entry shape: no engine, ho or fresh fields. *)
    val old_format_line =
      "{\"run\":\"fixture\",\"thy\":\"list\",\"thm\":\"one\"," ^
      "\"goal_id\":\"list.one\",\"cond\":\"deps-e\"," ^
      "\"regime\":\"bushy\",\"selector\":\"deps\",\"prover\":\"e\"," ^
      "\"prover_version\":null,\"nfacts\":3,\"timeout\":5," ^
      "\"szs\":\"Theorem\",\"t_prover\":0.2,\"axioms_used\":null," ^
      "\"recon_ok\":null,\"recon_method\":null,\"t_recon\":null," ^
      "\"stac\":null,\"error\":null}"
    val torn = hhEval.journal_path expdir "torn"
    val _ = write_file torn "{\"run\":\"fix\n"
    val _ = hhEval.append_journal torn sched_entry
    val _ = expect "resume skips torn journal lines"
      (hhEval.journal_complete torn [("list.scheduled", "sched")])
    val old_format = hhEval.journal_path expdir "old-format"
    val _ = write_file old_format (old_format_line ^ "\n")
    val _ = hhEval.append_journal old_format sched_entry
    val _ = expect "old-format journal entries are rejected, not skipped"
      (((hhEval.read_journal old_format; false)
        handle Fail message =>
          String.isSubstring "unsupported hhEval journal entry" message))
    val header : hhEval.run_header =
      {expname = "fixture", date = "today", host = "host", hol_commit = "abc",
       provers = [{prover = Eprover, path = SOME "/e", version = SOME "3.2.5",
                   sha256 = SOME "123"}],
       corpus = [{thy = "list", theorem_count = 2, dep_stamp = "stamp"}],
       added_from_dat = ["missing"], conditions = [condition], sample = 1}
    val _ = hhEval.write_run_header expdir header
    val header_json = JSONParser.parseFile (join expdir "run.json")
    val _ = expect "run header writer"
      (JSONUtil.asString (JSONUtil.lookupField header_json "expname") =
       "fixture" andalso
       JSONUtil.asInt (JSONUtil.lookupField header_json "schema") = 4)
    fun resume_header conditions sample corpus : hhEval.run_header =
      {expname = #expname header, date = "later", host = #host header,
       hol_commit = #hol_commit header, provers = #provers header,
       corpus = corpus, added_from_dat = #added_from_dat header,
       conditions = conditions, sample = sample}
    fun resume_rejected field requested =
      ((hhEval.validate_run_header expdir requested; false)
       handle Fail message => String.isSubstring field message)
    val _ = hhEval.validate_run_header expdir
      (resume_header [condition] 1 (#corpus header))
    fun changed_condition selector engine timeout reconstruct =
      {cond_id = #cond_id condition, regime = #regime condition,
       selector = selector, engine = engine, timeout = timeout,
       reconstruct = reconstruct} : hhEval.condition
    val changed_conditions =
      [changed_condition (#selector condition) (#engine condition)
         (#timeout condition + 1) (#reconstruct condition),
       changed_condition hhEval.Deps (#engine condition)
         (#timeout condition) (#reconstruct condition),
       changed_condition (#selector condition) (hhEval.Prover Vampire)
         (#timeout condition) (#reconstruct condition),
       changed_condition (#selector condition) (#engine condition)
         (#timeout condition) (not (#reconstruct condition))]
    val _ = expect "resume rejects changed conditions with the same ID"
      (List.all (fn changed => resume_rejected "conditions"
        (resume_header [changed] 1 (#corpus header))) changed_conditions)
    val _ = expect "resume rejects changed sampling and corpus"
      (resume_rejected "sample"
         (resume_header [condition] 2 (#corpus header)) andalso
       resume_rejected "corpus" (resume_header [condition] 1 []))
    val _ = expect "resume rejects changed runtime hammer options"
      (with_hh_options [("filter", "mepo")] (fn () =>
        resume_rejected "hammer_options" header))
    val legacy_header =
      case header_json of
          JSON.OBJECT fields => JSON.OBJECT
            (List.filter (fn (key, _) => key <> "hammer_options") fields)
        | _ => raise Fail "expected a run header object"
    val _ = write_file (join expdir "run.json")
      (JSONPrinter.valueToString legacy_header)
    val _ = expect "resume rejects headers without hammer settings"
      (resume_rejected "hammer_options" header)
    val _ = hhEval.write_run_header expdir header
    val _ = expect "sample one selects every goal"
      (hhEval.sample_goal 1 "list.nil")
    val _ = expect "sample selection is deterministic"
      (hhEval.sample_goal 7 "list.nil" = hhEval.sample_goal 7 "list.nil")
    val _ = expect "invalid sample factor is rejected"
      ((hhEval.sample_goal 0 "list.nil"; false) handle Fail _ => true)
    val worker_options =
      [("filter", "mepo"), ("format", "tf0"),
       ("type_enc", "mono_native"), ("lam_trans", "lifting"),
       ("preplay_timeout", "2.5"), ("minimize_timeout", "3.5"),
       ("mono_instances", "17"), ("debug_dir", "quoted \"directory\"")]
    val script = with_hh_options worker_options (fn () =>
      hhEval.write_evalscript expdir "list" [condition] 7)
    val script_text = String.concat (read_lines script)
    val _ = expect "worker script preserves runtime hammer options"
      (List.all (fn (key, value) => String.isSubstring
        ("hhConfig.hh_set (" ^ Portable.mlquote key ^ ", " ^
         Portable.mlquote value ^ ");") script_text) worker_options)
    val default_script = hhEval.write_evalscript expdir "list" [condition] 7
    val _ = expect "worker script preserves the default monomorph cap"
      (case #mono_instances (hhConfig.snapshot ()) of
           NONE => not (String.isSubstring
             "hhConfig.hh_set (\"mono_instances\""
             (String.concat (read_lines default_script)))
         | SOME _ => true)
    val _ = expect "worker script is beside its theory"
      (OS.Path.dir script = join src "one" andalso
       script = hhEval.evalscript_path expdir "list")
    val _ = expect "worker script loads hhEval"
      (String.isSubstring "load \"hhEval\";" script_text)
    val _ = expect "worker script initializes the simp-data exporter"
      (String.isSubstring "load \"BasicProvers\";" script_text)
    val _ = expect "worker script loads its theory"
      (String.isSubstring "load \"listTheory\";" script_text)
    val _ = expect "worker script establishes an isolated current theory"
      (String.isSubstring
        "Theory.new_theory \"hheval_worker_list\";" script_text)
    val _ = expect "worker script reflects condition settings"
      (String.isSubstring "hhEval.set_worker_settings" script_text andalso
       String.isSubstring "knn-e" script_text andalso
       String.isSubstring "sample = 7" script_text)
    val _ = expect "worker script calls eval_thy"
      (String.isSubstring "hhEval.eval_thy" script_text)
    val reportdir = join root "hheval-report"
    val report_journal = join reportdir "journal"
    val fixture_journal = join "test-data" "hheval-report/journal"
    fun copy_fixture name =
      write_file (join report_journal name)
        (String.concat (read_lines (join fixture_journal name)))
    val _ = remove_tree reportdir
    val _ = mkdirs report_journal
    val _ = copy_fixture "list.jsonl"
    val _ = copy_fixture "arithmetic.jsonl"
    val _ = copy_fixture "sched.jsonl"
    fun subset_entry thm ho fresh recon : hhEval.journal_entry =
      {run = #run full_entry, thy = "subset", thm = thm,
       goal_id = "subset." ^ thm, cond = "subset-fixture",
       regime = hhEval.Bushy, selector = hhEval.Deps,
       engine = SOME (hhEval.Prover Eprover), ho = ho, fresh = fresh,
       prover = SOME Eprover,
       prover_version = #prover_version full_entry, nfacts = 3, timeout = 6,
       szs = hhEval.Szs hhProver.SzsTheorem, t_prover = 0.1,
       axioms_used = NONE,
       recon_ok = recon, recon_method = NONE, t_recon = NONE, stac = NONE,
       error = NONE, stop = NONE, t_total = NONE, winner = NONE, slices = []}
    val subset_journal = join report_journal "subset.jsonl"
    val _ = hhEval.append_journal subset_journal
      (subset_entry "ho" true false (SOME true))
    val _ = hhEval.append_journal subset_journal
      (subset_entry "first_order" false true (SOME false))
    fun one_shot_entry cond thm selector : hhEval.journal_entry =
      {run = "fixture", thy = "ensemble", thm = thm,
       goal_id = "ensemble." ^ thm, cond = cond,
       regime = hhEval.Chainy, selector = selector,
       engine = SOME (hhEval.Prover Eprover), ho = false, fresh = false,
       prover = SOME Eprover, prover_version = SOME "3.2.5", nfacts = 96,
       timeout = 17, szs = hhEval.Szs hhProver.SzsTheorem,
       t_prover = 0.2,
       axioms_used = NONE, recon_ok = SOME true,
       recon_method = SOME "metis", t_recon = SOME 0.1,
       stac = SOME "metis_tac []", error = NONE, stop = NONE,
       t_total = NONE, winner = NONE, slices = []}
    val ensemble_journal = join report_journal "ensemble.jsonl"
    val _ = hhEval.append_journal ensemble_journal
      (one_shot_entry "report-mepo" "mepo" (hhEval.Mepo 96))
    val _ = hhEval.append_journal ensemble_journal
      (one_shot_entry "report-mash" "mash" (hhEval.Mash 96))
    val _ = hhEval.append_journal ensemble_journal
      (one_shot_entry "report-mesh" "mesh" (hhEval.Mesh 96))
    val collision_engine = hhEval.Sched
      {provers = [Z3], slices = 1, cores = 1, max_proofs = 1,
       export_workers = 1}
    fun collision_slice filter : hhProver.slice =
      {prover = Z3, format = "fof", type_enc = "",
       lam_trans = "", nfacts = 77, filter = filter,
       extra_opts = [], slice_size = 1}
    fun collision_entry thm filter recon : hhEval.journal_entry =
      let
        val slice = collision_slice filter
        val journal_slice : hhEval.journal_slice =
          {slice = slice, szs = hhProver.SzsTheorem, time = 0.3,
           cached = false}
      in
        {run = "fixture", thy = "collision", thm = thm,
         goal_id = "collision." ^ thm, cond = "filter-collision",
         regime = hhEval.Chainy, selector = hhEval.PerSlice,
         engine = SOME collision_engine, ho = false, fresh = false,
         prover = SOME Z3, prover_version = SOME "fixture",
         nfacts = 77, timeout = 19, szs = hhEval.Szs hhProver.SzsTheorem,
         t_prover = 0.3,
         axioms_used = NONE, recon_ok = SOME recon,
         recon_method = SOME "metis", t_recon = SOME 0.1,
         stac = SOME "metis_tac []", error = NONE, stop = SOME "MaxProofs",
         t_total = SOME 0.4, winner = SOME slice, slices = [journal_slice]}
      end
    val collision_journal = join report_journal "collision.jsonl"
    val _ = hhEval.append_journal collision_journal
      (collision_entry "mepo" "mepo" true)
    val _ = hhEval.append_journal collision_journal
      (collision_entry "mesh" "mesh" false)
    val report_corrupt = TextIO.openAppend (join report_journal "list.jsonl")
    val _ = TextIO.output (report_corrupt, "{in-progress")
    val _ = TextIO.closeOut report_corrupt
    val _ = hhEval.report reportdir
    val summary = JSONParser.parseFile (join reportdir "summary.json")
    fun array_field name value =
      JSONUtil.arrayMap (fn item => item) (JSONUtil.lookupField value name)
    fun named name wanted values =
      case List.find (fn value =>
        JSONUtil.asString (JSONUtil.lookupField value name) = wanted) values of
          SOME value => value
        | NONE => raise Fail ("missing report item: " ^ wanted)
    fun metric name value =
      JSONUtil.asInt (JSONUtil.lookupField
        (JSONUtil.lookupField value "metrics") name)
    val conditions = array_field "conditions" summary
    val e_condition = named "cond" "deps-e" conditions
    val vampire_condition = named "cond" "deps-vampire" conditions
    val sched_condition = named "cond" "sched-main" conditions
    val subset_condition = named "cond" "subset-fixture" conditions
    val mepo_condition = named "cond" "report-mepo" conditions
    val mash_condition = named "cond" "report-mash" conditions
    val mesh_condition = named "cond" "report-mesh" conditions
    val subset_rows = array_field "subsets" subset_condition
    val ho_subset = named "subset" "HO" subset_rows
    val non_ho_subset = named "subset" "non-HO" subset_rows
    val fresh_rows = array_field "fresh_subsets" subset_condition
    val seen_subset = named "subset" "seen" fresh_rows
    val fresh_subset = named "subset" "fresh" fresh_rows
    val portfolios = array_field "portfolios" summary
    val portfolio = named "key" "bushy/5s" portfolios
    val prover_rows = array_field "provers" portfolio
    val e_prover = named "prover" "e" prover_rows
    val vampire_prover = named "prover" "vampire" prover_rows
    val report_text = String.concat (read_lines (join reportdir "report.md"))
    val _ = expect "report writes both output files"
      (OS.FileSys.access (join reportdir "summary.json", [OS.FileSys.A_READ])
       andalso
       OS.FileSys.access (join reportdir "report.md", [OS.FileSys.A_READ]))
    val _ = expect "report condition counts and quantiles"
      (metric "goals" e_condition = 5 andalso
       metric "attempted" e_condition = 4 andalso
       metric "proved" e_condition = 2 andalso
       metric "reconstructed" e_condition = 1 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField e_condition "metrics") "t_prover_p50"))
         0.2 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField e_condition "metrics") "t_prover_p90"))
         1.0 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField e_condition "metrics") "t_prover_max"))
         1.0 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField e_condition "metrics") "proved_pct"))
         50.0 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField e_condition "metrics") "reconstructed_pct"))
         25.0)
    val _ = expect "report second prover counts"
      (metric "goals" vampire_condition = 5 andalso
       metric "attempted" vampire_condition = 4 andalso
       metric "proved" vampire_condition = 3 andalso
       metric "reconstructed" vampire_condition = 2)
    val _ = expect "report schedule counts and total-time quantiles"
      (metric "goals" sched_condition = 4 andalso
       metric "attempted" sched_condition = 4 andalso
       metric "proved" sched_condition = 3 andalso
       metric "reconstructed" sched_condition = 2 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField sched_condition "metrics") "t_prover_p50"))
         0.8 andalso
       same_real (JSONUtil.asNumber (JSONUtil.lookupField
         (JSONUtil.lookupField sched_condition "metrics") "t_prover_p90"))
         1.2)
    val _ = expect "report portfolio union and unique solves"
      (metric "goals" portfolio = 6 andalso
       metric "attempted" portfolio = 5 andalso
       metric "proved" portfolio = 4 andalso
       metric "reconstructed" portfolio = 2 andalso
       JSONUtil.asInt (JSONUtil.lookupField e_prover "unique_proved") =
         1 andalso
       JSONUtil.asInt (JSONUtil.lookupField vampire_prover "unique_proved") =
         2 andalso
       JSONUtil.asInt (JSONUtil.lookupField e_prover
         "unique_reconstructed") = 0 andalso
       JSONUtil.asInt (JSONUtil.lookupField vampire_prover
         "unique_reconstructed") = 1)
    val _ = expect "report includes per-theory markdown table"
      (String.isSubstring "## Theories" report_text andalso
       String.isSubstring "| arithmetic | deps-e" report_text andalso
       String.isSubstring "| list | deps-vampire" report_text)
    val distributions = array_field "schedule_distributions" summary
    val sched_distribution = named "cond" "sched-main" distributions
    val stop_rows = array_field "stop_reasons" sched_distribution
    val max_proofs = named "value" "MaxProofs" stop_rows
    val comparisons = array_field "schedule_vs_union" summary
    val comparison = named "condition" "sched-main" comparisons
    val contributions = array_field "slice_contributions" summary
    fun collision_contribution filter =
      List.filter (fn row =>
        JSONUtil.asString (JSONUtil.lookupField row "format") = "fof" andalso
        JSONUtil.asString (JSONUtil.lookupField row "type_enc") = "" andalso
        JSONUtil.asString (JSONUtil.lookupField row "lam_trans") = "" andalso
        JSONUtil.asString (JSONUtil.lookupField row "prover") = "z3"
        andalso
        JSONUtil.asInt (JSONUtil.lookupField row "nfacts") = 77 andalso
        JSONUtil.asString (JSONUtil.lookupField row "filter") = filter)
        contributions
    val _ = expect "report HO subset arithmetic and slice contributions"
      (metric "goals" ho_subset = 1 andalso
       metric "proved" ho_subset = 1 andalso
       metric "reconstructed" ho_subset = 1 andalso
       metric "goals" non_ho_subset = 1 andalso
       metric "proved" non_ho_subset = 1 andalso
       metric "reconstructed" non_ho_subset = 0 andalso
       List.exists (fn row =>
         JSONUtil.asString (JSONUtil.lookupField row "format") = "fof" andalso
         JSONUtil.asInt (JSONUtil.lookupField row "wins") >= 1)
         contributions andalso
       String.isSubstring "## HO subsets" report_text andalso
       String.isSubstring "| deps-e | HO | 0 | 0 | 0 | - |" report_text andalso
       String.isSubstring "## Slice contributions" report_text)
    val _ = expect "report seen/fresh arithmetic and filter keys"
      (JSONUtil.asString (JSONUtil.lookupField subset_condition "filter") =
         "deps" andalso
       metric "goals" seen_subset = 1 andalso
       metric "proved" seen_subset = 1 andalso
       metric "reconstructed" seen_subset = 1 andalso
       metric "goals" fresh_subset = 1 andalso
       metric "proved" fresh_subset = 1 andalso
       metric "reconstructed" fresh_subset = 0 andalso
       List.exists (fn row =>
         JSONUtil.asString (JSONUtil.lookupField row "filter") = "mepo")
         contributions andalso
       String.isSubstring "## Seen/fresh subsets" report_text andalso
       String.isSubstring "| subset-fixture | deps | seen | 1 |" report_text)
    val _ = expect "report labels every one-shot ensemble filter"
      (JSONUtil.asString (JSONUtil.lookupField mepo_condition "filter") =
         "mepo" andalso
       JSONUtil.asString (JSONUtil.lookupField mash_condition "filter") =
         "mash" andalso
       JSONUtil.asString (JSONUtil.lookupField mesh_condition "filter") =
         "mesh" andalso
       String.isSubstring "| report-mepo | e | mepo |" report_text andalso
       String.isSubstring "| report-mash | e | mash |" report_text andalso
       String.isSubstring "| report-mesh | e | mesh |" report_text)
    val _ = expect "slice contributions distinguish filter-only collisions"
      (case (collision_contribution "mepo",
             collision_contribution "mesh") of
           ([mepo], [mesh]) =>
             JSONUtil.asInt (JSONUtil.lookupField mepo "wins") = 1 andalso
             JSONUtil.asInt
               (JSONUtil.lookupField mepo "reconstructed") = 1 andalso
             JSONUtil.asInt (JSONUtil.lookupField mesh "wins") = 1 andalso
             JSONUtil.asInt
               (JSONUtil.lookupField mesh "reconstructed") = 0
         | _ => false)
    val _ = expect "report schedule distributions"
      (JSONUtil.asInt (JSONUtil.lookupField max_proofs "count") = 2 andalso
       length (array_field "slices_run" sched_distribution) = 2 andalso
       String.isSubstring "2:1, 3:3" report_text andalso
       String.isSubstring "MaxProofs:2" report_text)
    val _ = expect "report schedule versus union comparison"
      (JSONUtil.asInt (JSONUtil.lookupField comparison "proved_delta") = ~1
       andalso JSONUtil.asInt
         (JSONUtil.lookupField comparison "reconstructed_delta") = 0 andalso
       String.isSubstring "## Schedule vs portfolio union" report_text andalso
       String.isSubstring "| sched-main | bushy/5s | 3 | 4 | -1 | 2 | 2 | 0 |"
         report_text)
  in
    ()
  end

val _ =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      NONE => ()
    | SOME root => test_hhEval root

fun test_actual_hhEval_corpus () =
  let
    val theories = hhEval.stdlib_theories ()
    val coverage = hhEval.stdlib_coverage ()
    val _ = expect "stdlib corpus contains list and arithmetic"
      (List.exists (fn theory => theory = "list") theories andalso
       List.exists (fn theory => theory = "arithmetic") theories)
    val _ = expect "stdlib coverage discrepancies are recorded"
      (List.all (fn theory => List.exists (fn item => item = theory) theories)
       (#added_from_dat coverage))
  in
    ()
  end

val _ =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      NONE => test_actual_hhEval_corpus ()
    | SOME _ => ()

fun test_holyHammer_e () =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      SOME _ => ()
    | NONE =>
        case hhProver.probe (prover Eprover) of
            NONE =>
              (tprint "holyHammer end-to-end e (skipped: absent)"; OK ())
          | SOME _ =>
              let
                val root = OS.FileSys.tmpName ()
                val _ = remove_tree root
                val _ = mkdir root
                val add1 = DB.fetch "arithmetic" "ADD1"
                val output = OS.Path.concat (root, "stdout")
                fun call () =
                  (ignore (holyHammer.hh_pb root [Eprover]
                     ["arithmeticTheory.ADD1"] (Thm.dest_thm add1));
                   TextIO.flushOut TextIO.stdOut)
                val success =
                  ((holyHammer.set_timeout 10;
                    TextIO.flushOut TextIO.stdOut;
                    smlRedirect.hide_in_file output call ();
                    true)
                   handle Interrupt =>
                     raise Interrupt
                        | Feedback.HOL_ERR error =>
                     (print (Feedback.message_of error ^ "\n"); false)
                        | exn =>
                     (print (General.exnMessage exn ^ "\n"); false))
                val _ = hhConfig.hh_unset "timeout"
                val printed =
                  if success then aiLib.readl output else []
                val _ = remove_tree root
                (* The tactic to use is the last thing printed, after
                   every slice has reported. *)
                val announced_last =
                  case List.rev printed of
                      tactic :: heading :: _ =>
                        heading = "Replace `hh_pb` with:" andalso
                        String.isPrefix "  " tactic andalso
                        String.isSubstring "ADD1" tactic
                    | _ => false
              in
                expect "holyHammer hh_pb end-to-end e" success;
                expect "holyHammer hh_pb ends with the tactic to use"
                  announced_last
              end

(* Metis replays the lemma lists below in milliseconds, or runs until
   it is stopped. *)
fun reconstruct_timed minimize timeout deadline lemmas goal =
  let
    val started = Time.now ()
    val result =
      SOME (smlRedirect.hidef (hhReconstruct.hh_reconstruct_with
        {minimize = minimize, preplay_timeout = timeout,
         minimize_timeout = timeout, minimize_deadline = deadline}
        lemmas) goal)
      handle Interrupt => raise Interrupt | Feedback.HOL_ERR _ => NONE
  in
    (result, Time.toReal (Time.- (Time.now (), started)))
  end

fun replays_in_kernel goal ({tac, ...} : hhReconstruct.reconstruction) =
  (ignore (Tactical.TAC_PROOF (goal, tac)); true)
  handle Interrupt => raise Interrupt | _ => false

fun test_hhReconstruct () =
  let
    val arith = map (fn name => "arithmeticTheory." ^ name)
    val false_goal = ([], ``!n. n + 1 = n``)
    val false_lemmas =
      arith ["ADD_COMM", "ADD_ASSOC", "ADD_CLAUSES", "MULT_COMM",
             "LEFT_ADD_DISTRIB", "ADD1"]
    (* Each of the seven attempts used to run out the full timeout. *)
    val (failed, failed_time) =
      reconstruct_timed true 0.5 NONE false_lemmas false_goal
    val _ = expect "reconstruction of an unreplayable list fails at once"
      (not (Option.isSome failed) andalso failed_time < 2.0)
    (* The step case of LENGTH (flatten t) = size t, with the tree's
       recursion equations as hypotheses.  Metis replays the list in
       about 0.03 s without the permutative ADD_SYM and needs over 1 s
       with it. *)
    val step_goal =
      ([], ``fl = a ++ ([x] ++ b) ++ [y] /\ s = m + 1 + n + 1 /\
             LENGTH a = m /\ LENGTH b = n ==> LENGTH fl = s``)
    val step_lemmas =
      arith ["ADD_SYM", "ADD_ASSOC", "SUC_ONE_ADD", "NUMERAL_DEF",
             "ALT_ZERO", "ADD_CLAUSES"] @
      map (fn name => "listTheory." ^ name)
        ["APPEND_ASSOC", "LENGTH", "LENGTH_APPEND"]
    val (repaired, _) =
      reconstruct_timed false 0.3 NONE step_lemmas step_goal
    val _ = expect "a list blocked by a permutative lemma replays without it"
      (case repaired of
           SOME (result as {stac, ...}) =>
             not (String.isSubstring "ADD_SYM" stac) andalso
             String.isSubstring "LENGTH_APPEND" stac andalso
             replays_in_kernel step_goal result
         | NONE => false)
    val goal = ([], ``x * (y + z) = z * x + x * y : num``)
    val lemmas =
      arith ["ADD_ASSOC", "LEFT_ADD_DISTRIB", "ADD_COMM", "MULT_COMM",
             "MULT_ASSOC"]
    (* Without LEFT_ADD_DISTRIB, Metis runs until it is stopped. *)
    val (minimized, minimize_time) =
      reconstruct_timed true 10.0 NONE lemmas goal
    val _ = expect "minimisation attempts are bounded by the replay time"
      (case minimized of
           SOME (result as {stac, t_replay, ...}) =>
             String.isSubstring "LEFT_ADD_DISTRIB" stac andalso
             not (String.isSubstring "ASSOC" stac) andalso
             t_replay < 10.0 andalso replays_in_kernel goal result
         | NONE => false)
    val _ = expect "minimisation without a needed lemma stays fast"
      (minimize_time < 5.0)
    val (unminimized, _) =
      reconstruct_timed true 10.0 (SOME (Time.now ())) lemmas goal
    val _ = expect "minimisation past its deadline keeps the verified list"
      (case unminimized of
           SOME (result as {stac, ...}) =>
             List.all (fn name => String.isSubstring name stac)
               ["ADD_ASSOC", "LEFT_ADD_DISTRIB", "ADD_COMM", "MULT_COMM",
                "MULT_ASSOC"] andalso
             replays_in_kernel goal result
         | NONE => false)
    (* A theorem of the current theory has no Theory structure.  The
       proof names it by the top-level ML value bound to it, as Theorem
       binds it in a script, and else fetches it from DB.  A theorem of
       an ancestor is named by a value of its name that is a copy, as
       rich_list's MAP_REVERSE is of list's. *)
    val thy = Theory.current_theory ()
    fun save name = ignore
      (Feedback.quiet_messages Theory.save_thm (name, arithmeticTheory.ADD_0))
    val _ = app save ["hh_bound_add0", "hh_int_add0", "hh_other_add0"]
    val _ = smlExecute.quse_string
      ("val hh_bound_add0 = DB.fetch " ^ Lib.quote thy ^
       " \"hh_bound_add0\"; val hh_int_add0 = 0; " ^
       "val hh_other_add0 = arithmeticTheory.ADD_COMM; " ^
       "val ADD_0 = Drule.GEN_ALL (Drule.SPEC_ALL arithmeticTheory.ADD_0);")
    val add0_goal = ([], ``x + 0 = x``)
    fun stac_in theory name =
      case #1 (reconstruct_timed true 1.0 NONE [theory ^ "Theory." ^ name]
                  add0_goal) of
          SOME (result as {stac, ...}) =>
            if replays_in_kernel add0_goal result then stac else ""
        | NONE => ""
    val stac_of = stac_in thy
    fun fetched name =
      String.isSubstring
        ("fetch " ^ Lib.quote thy ^ " " ^ Lib.quote name ^ "]")
        (stac_of name)
    val _ = expect "a current-theory lemma is named by its ML value"
      (String.isSuffix " [hh_bound_add0]" (stac_of "hh_bound_add0"))
    val _ = expect "a lemma whose name is not bound to it is fetched"
      (fetched "hh_int_add0" andalso fetched "hh_other_add0")
    val _ = expect "an ancestor's lemma is named by a copy bound to its name"
      (String.isSuffix " [ADD_0]" (stac_in "arithmetic" "ADD_0"))
  in
    ()
  end

val _ = test_hhReconstruct ()

val _ = test_szs_status_words ()
val _ = test_hhProver ()
val _ = test_hhSlice ()
val _ = test_hhCache ()
val _ = test_holyHammer_validation ()
val _ = test_runner ()
val _ = test_installed_provers ()
val _ = test_holyHammer_e ()

val schedule_fixture_dir = "test-data"
val schedule_printer = join schedule_fixture_dir "runner-print-e.sh"
val schedule_sleeper =
  join schedule_fixture_dir "runner-forking-sleeper.sh"

fun fixture_slice prover extra size : hhProver.slice =
  {prover = prover, format = "fof", type_enc = "", lam_trans = "",
   nfacts = 0, filter = "none", extra_opts = extra, slice_size = size}

fun ranking_fixture_slice prover filter nfacts : hhProver.slice =
  {prover = prover, format = "fof", type_enc = "", lam_trans = "",
   nfacts = nfacts, filter = filter,
   extra_opts = ["0", "e-gave-up.out"], slice_size = 1}

fun printer_config_formats formats name slices note parser
    : hhProver.prover_config =
  {name = name, exec_names = [schedule_printer], env_var = "",
   version_args = ["--version"], parse_version = fn _ => SOME "test",
   tested_versions = ["test"], supported_formats = formats,
   mk_command = fn executable => fn request =>
     (note request; (executable, #extra request)),
   parse_output = parser, mono_instances = 100,
   slices = slices, legacy = false}

fun printer_config name slices note parser =
  printer_config_formats ["fof"] name slices note parser

fun sleeper_config prover name parser : hhProver.prover_config =
  let val slice = fixture_slice prover [] 1 in
    {name = name, exec_names = [schedule_sleeper], env_var = "",
     version_args = ["--version"], parse_version = fn _ => SOME "test",
     tested_versions = ["test"], supported_formats = ["fof"],
     mk_command = fn executable => fn _ => (executable, []),
     parse_output = parser, mono_instances = 100,
     slices = [slice], legacy = false}
  end

fun fixture_options provers slices cores timeout max_proofs cache cache_dir
    debug_dir : hhConfig.hh_options =
  {timeout = timeout, max_proofs = max_proofs, provers = provers,
   slices = slices, cores = cores,
   export_workers = 1,
   filter = "none", max_facts = NONE,
   format = "", type_enc = "", lam_trans = "", mono_iters = 3,
   mono_instances = NONE, minimize = true, preplay_timeout = 1.0,
   minimize_timeout = 1.0,
   cache = cache, cache_dir = cache_dir, cache_max_entries = 100,
   debug_dir = debug_dir,
   preplay_drop_one = false, verbose = false}

(* A fixture prover_config stands in for a built-in prover while f runs.
   Its name stays its own, so its output files and probe results are not
   mistaken for the built-in prover's. *)
fun with_fixtures [] f = f ()
  | with_fixtures ((prover, config) :: rest) f =
      hhProver.with_override prover config (fn () => with_fixtures rest f)

fun reconstruction_options {minimize, preplay_drop_one}
    (options : hhConfig.hh_options) : hhConfig.hh_options =
  {timeout = #timeout options, max_proofs = #max_proofs options,
   provers = #provers options, slices = #slices options,
   cores = #cores options,
   export_workers = 1,
   filter = #filter options,
   max_facts = #max_facts options, format = #format options,
   type_enc = #type_enc options, lam_trans = #lam_trans options,
   mono_iters = #mono_iters options, mono_instances = #mono_instances options,
   minimize = minimize, preplay_timeout = #preplay_timeout options,
   minimize_timeout = #minimize_timeout options, cache = #cache options,
   cache_dir = #cache_dir options,
   cache_max_entries = #cache_max_entries options,
   debug_dir = #debug_dir options,
   preplay_drop_one = preplay_drop_one, verbose = #verbose options}

fun slice_event_tag (slice : hhProver.slice) =
  hhConfig.prover_name (#prover slice) ^ ":" ^
  String.concatWith "," (#extra_opts slice)

fun stop_event_name hhSchedule.MaxProofs = "max-proofs"
  | stop_event_name hhSchedule.Timeout = "timeout"
  | stop_event_name hhSchedule.Exhausted = "exhausted"
  | stop_event_name hhSchedule.Interrupted = "interrupted"

fun szs_event_name hhProver.SzsTheorem = "theorem"
  | szs_event_name hhProver.SzsCounterSat = "counter-sat"
  | szs_event_name hhProver.SzsSatisfiable = "satisfiable"
  | szs_event_name hhProver.SzsGaveUp = "gave-up"
  | szs_event_name hhProver.SzsTimeout = "timeout"
  | szs_event_name hhProver.SzsResourceOut = "resource-out"
  | szs_event_name hhProver.SzsInappropriate = "inappropriate"
  | szs_event_name (hhProver.SzsUnknown status) = status
  | szs_event_name (hhProver.RunFailure message) = "failure:" ^ message

fun observe_schedule_event (hhSchedule.SliceStarted slice) =
      "started|" ^ slice_event_tag slice
  | observe_schedule_event (hhSchedule.SliceDone (slice, _, _)) =
      "done|" ^ slice_event_tag slice
  | observe_schedule_event (hhSchedule.ProofFound (slice, _)) =
      "found|" ^ slice_event_tag slice
  | observe_schedule_event (hhSchedule.Verified suggestion) =
      "verified|" ^ slice_event_tag (#slice suggestion)
  | observe_schedule_event (hhSchedule.ScheduleDone reason) =
      "schedule-done|" ^ stop_event_name reason

fun run_schedule_on goal options =
  let
    val events = ref ([] : string list)
    val result = hhSchedule.run
      {options = options, goal = goal, rankings = [("none", [])],
       progress = SOME (fn event =>
         events := observe_schedule_event event :: !events)}
  in
    (result, List.rev (!events))
  end

fun run_schedule options = run_schedule_on ([], boolSyntax.T) options

fun event_position wanted events =
  let
    fun seek _ [] = NONE
      | seek index (event :: rest) =
          if event = wanted then SOME index else seek (index + 1) rest
  in
    seek 0 events
  end

fun event_before left right events =
  case (event_position left events, event_position right events) of
      (SOME left_index, SOME right_index) => left_index < right_index
    | _ => false

fun event_suffix prefix event =
  String.extract (event, String.size prefix, NONE)

fun schedule_events_sane events =
  let
    fun with_prefix prefix = List.filter (String.isPrefix prefix) events
    fun follows earlier prefix event =
      event_before (earlier ^ event_suffix prefix event) event events
    val done = with_prefix "done|"
    val found = with_prefix "found|"
    val verified = with_prefix "verified|"
    val finished = with_prefix "schedule-done|"
  in
    not (null events) andalso length finished = 1 andalso
    hd (List.rev events) = hd finished andalso
    List.all (follows "started|" "done|") done andalso
    List.all (follows "done|" "found|") found andalso
    List.all (follows "found|" "verified|") verified
  end

fun output_files directory name =
  map (join directory)
    (List.filter (String.isPrefix (name ^ "-"))
      (hhConfig.directory_names directory))

fun fixture_child_gone directory name =
  case output_files directory name of
      [path] =>
        let
          val pid = pid_from_output (String.concat (read_lines path))
        in
          wait_until (Time.+ (Time.now (), Time.fromSeconds 5))
            (fn () => process_is_gone pid)
        end
    | _ => false

fun test_schedule_max_proofs parser =
  let
    val name = "hh-schedule-max-proofs"
    val slices =
      [fixture_slice Z3 ["0", "schedule-truth.out"] 1,
       fixture_slice Z3 ["0", "schedule-t-def.out"] 1]
    (* The problem files are deleted after the run, so check them while
       the prover runs. *)
    val paths = ref ([] : (string * bool) list)
    fun readable path = OS.FileSys.access (path, [OS.FileSys.A_READ])
    val config = printer_config name slices
      (fn request =>
         paths := (#problem request, readable (#problem request)) :: !paths)
      parser
    val options1 = fixture_options [Z3] 2 2 5 1 false "" NONE
    val options2 = fixture_options [Z3] 2 2 5 2 false "" NONE
    val ((result1, _), (result2, events2)) =
      with_fixtures [(Z3, config)] (fn () =>
        (run_schedule options1, run_schedule options2))
    val lemma_sets = map (#lemmas : hhSchedule.suggestion -> string list)
      (#suggestions result2)
    val _ = expect "scheduler max_proofs one stops after one verification"
      (#stopped result1 = hhSchedule.MaxProofs andalso
       length (#suggestions result1) = 1)
    val _ = expect "scheduler max_proofs two verifies two suggestions"
      (#stopped result2 = hhSchedule.MaxProofs andalso
       length (#suggestions result2) = 2 andalso
       List.exists (fn lemmas => lemmas = ["boolTheory.TRUTH"])
         lemma_sets andalso
       List.exists (fn lemmas => lemmas = ["boolTheory.T_DEF"])
         lemma_sets)
    val _ = expect "scheduler suggestions carry their replay time"
      (List.all (fn {t_replay, t_recon, ...} : hhSchedule.suggestion =>
          0.0 <= t_replay andalso t_replay <= t_recon)
         (#suggestions result2))
    val _ = expect "scheduler event ordering is sane"
      (schedule_events_sane events2)
    val _ = expect "scheduler exports the zero-fact prefix"
      (not (null (!paths)) andalso List.all #2 (!paths))
    val _ = expect "scheduler removes its problem files"
      (List.all (fn (path, _) => not (readable path)) (!paths))
  in
    ()
  end

fun test_schedule_reconstruction_failure parser =
  let
    val name = "hh-schedule-reconstruction-failure"
    val bad_recording = "schedule-unreconstructable.out"
    val slices =
      [fixture_slice Z3 ["0", bad_recording] 1,
       fixture_slice Z3 ["0", "schedule-add1.out"] 1]
    val config = printer_config name slices (fn _ => ()) parser
    val (bad_status, bad_axioms) =
      parser (read_lines (join schedule_fixture_dir bad_recording))
    val (good_status, good_axioms) =
      parser
        (read_lines (join schedule_fixture_dir "schedule-add1.out"))
    val options = fixture_options [Z3] 2 1 5 1 false "" NONE
    val goal = ([], Thm.concl (DB.fetch "arithmetic" "ADD1"))
    val (result, events) =
      with_fixtures [(Z3, config)] (fn () => run_schedule_on goal options)
    val found = List.filter (String.isPrefix "found|") events
    val verified = List.filter (String.isPrefix "verified|") events
    val _ = expect "unreconstructable scheduler recording parses as theorem"
      (bad_status = hhProver.SzsTheorem andalso
       bad_axioms = SOME ["fixtureTheory.unreconstructable"])
    val _ = expect "replayable scheduler recording parses as theorem"
      (good_status = hhProver.SzsTheorem andalso
       good_axioms = SOME ["arithmeticTheory.ADD1"])
    val _ = expect "both reconstruction results are discovered"
      (length found = 2)
    val _ = expect "only the replayable reconstruction verifies"
      (length verified = 1)
    val _ = expect "failed reconstruction does not stop the schedule"
      (#stopped result = hhSchedule.MaxProofs andalso
       case #suggestions result of
           [suggestion] =>
             #lemmas suggestion = ["arithmeticTheory.ADD1"]
         | _ => false)
  in
    ()
  end

fun test_schedule_without_minimization () =
  let
    val name = "hh-schedule-no-minimize"
    val lemmas = ["boolTheory.TRUTH", "boolTheory.T_DEF"]
    val slice = fixture_slice Z3 ["0", "schedule-truth.out"] 1
    val config = printer_config name [slice] (fn _ => ())
      (fn _ => (hhProver.SzsTheorem, SOME lemmas))
    val options =
      reconstruction_options {minimize = false, preplay_drop_one = false}
      (fixture_options [Z3] 1 1 5 1 false "" NONE)
    val (result, _) =
      with_fixtures [(Z3, config)] (fn () => run_schedule options)
    val _ = expect "scheduler minimize=false preserves the ATP lemma list"
      (case #suggestions result of
           [suggestion] => #stac suggestion = mlThmData.mk_metis_call lemmas
         | _ => false)
  in
    ()
  end

(* Five slices report the same list, which Metis cannot replay within
   preplay_timeout (1 s).  Replaying it once per slice took 5 s. *)
(* fixtureTheory.unreconstructable does not exist, so Metis cannot replay
   the list; without it the list proves ADD1. *)
fun test_schedule_drop_one () =
  let
    val name = "hh-schedule-drop-one"
    val lemmas = ["fixtureTheory.unreconstructable", "arithmeticTheory.ADD1"]
    val slice = fixture_slice Z3 ["0", "schedule-truth.out"] 1
    val config = printer_config name [slice] (fn _ => ())
      (fn _ => (hhProver.SzsTheorem, SOME lemmas))
    val goal = ([], Thm.concl (DB.fetch "arithmetic" "ADD1"))
    fun run preplay_drop_one =
      #1 (with_fixtures [(Z3, config)] (fn () =>
        run_schedule_on goal
          (reconstruction_options
             {minimize = true, preplay_drop_one = preplay_drop_one}
             (fixture_options [Z3] 1 1 5 1 false "" NONE))))
    val plain = run false
    val retried = run true
  in
    expect "an unreplayable list fails without preplay_drop_one"
      (null (#suggestions plain) andalso
       #stopped plain = hhSchedule.Exhausted);
    expect "preplay_drop_one replays the list less a lemma"
      (case #suggestions retried of
           [suggestion] => #lemmas suggestion = ["arithmeticTheory.ADD1"]
         | _ => false)
  end

fun test_schedule_failed_list_once () =
  let
    val name = "hh-schedule-failed-list-once"
    val lemmas =
      map (fn lemma => "arithmeticTheory." ^ lemma)
        ["ADD_COMM", "ADD_ASSOC", "ADD_CLAUSES", "MULT_COMM",
         "LEFT_ADD_DISTRIB", "ADD1"]
    val slices =
      List.tabulate (5, fn index =>
        fixture_slice Z3 ["0", "schedule-truth.out", Int.toString index]
          1)
    val config = printer_config name slices (fn _ => ())
      (fn _ => (hhProver.SzsTheorem, SOME lemmas))
    val options = fixture_options [Z3] 5 5 20 1 false "" NONE
    val (result, events) = with_fixtures [(Z3, config)] (fn () =>
      run_schedule_on ([], ``!n. n + 1 = n``) options)
    val found = List.filter (String.isPrefix "found|") events
  in
    expect "scheduler replays a lemma list that failed only once"
      (length found = 5 andalso null (#suggestions result) andalso
       #stopped result = hhSchedule.Exhausted andalso
       #t_total result < 3.0)
  end

fun test_schedule_early_stop parser =
  let
    val slow1 = "hh-schedule-slow-one"
    val fast = "hh-schedule-fast"
    val slow2 = "hh-schedule-slow-two"
    val fast_slices =
      [fixture_slice Vampire ["2", "schedule-truth.out"] 1]
    val debug = OS.FileSys.tmpName ()
    val _ = remove_tree debug
    val fixtures =
      [(Eprover, sleeper_config Eprover slow1 parser),
       (Vampire, printer_config fast fast_slices (fn _ => ()) parser),
       (Zipperposition, sleeper_config Zipperposition slow2 parser)]
    val cache = join debug "cache"
    val options =
      fixture_options [Eprover, Vampire, Zipperposition] 3 3 12 1 true cache
        (SOME debug)
    val (result, events) =
      with_fixtures fixtures (fn () => run_schedule options)
    val children_gone =
      fixture_child_gone debug slow1 andalso fixture_child_gone debug slow2
    val early_stop_ok =
      #stopped result = hhSchedule.MaxProofs andalso
      length (#suggestions result) = 1
    val _ =
      if early_stop_ok then ()
      else
        print ("early-stop diagnostic: stopped=" ^
          stop_event_name (#stopped result) ^ ", suggestions=" ^
          Int.toString (length (#suggestions result)) ^ ", slices=" ^
          Int.toString (length (#slices_run result)) ^ ", total=" ^
          Real.toString (#t_total result) ^ ", events=" ^
          String.concatWith ";" events ^ ", results=" ^
          String.concatWith ";"
            (map (fn (slice, status, elapsed, _) =>
              slice_event_tag slice ^ ":" ^ szs_event_name status ^ ":" ^
              Real.toString elapsed) (#slices_run result)) ^ "\n")
    val _ = expect "scheduler early stop follows a verified proof"
      early_stop_ok
    val _ = expect "scheduler early stop returns below the slice budget"
      (#t_total result < 8.0)
    val _ = expect "scheduler early stop kills laggard process groups"
      children_gone
    val _ = expect "proof success caches only the completed slice"
      (length (hhConfig.directory_names cache) = 1)
    val _ = remove_tree debug
  in
    ()
  end

fun test_schedule_budget_truncation parser =
  let
    val name = "hh-schedule-budget"
    val first = fixture_slice Z3 ["2", "e-gave-up.out"] 1
    val second = fixture_slice Z3 ["0", "e-gave-up.out"] 4
    val budgets = ref ([] : int list)
    fun note (request : hhProver.run_request) =
      budgets := !budgets @ [#timeout request]
    val config = printer_config name [first, second] note parser
    val options = fixture_options [Z3] 2 1 4 1 false "" NONE
    val (result, _) =
      with_fixtures [(Z3, config)] (fn () => run_schedule options)
    val wanted = Real.ceil (hhSlice.slice_budget 2 options second)
    val _ = expect "late scheduler slice receives a truncated budget"
      (#stopped result = hhSchedule.Exhausted andalso
       case !budgets of
           [first_budget, second_budget] =>
             first_budget = 2 andalso second_budget < wanted
         | _ => false)
  in
    ()
  end

fun test_schedule_cache parser =
  let
    val name = "hh-schedule-cache"
    val slice = fixture_slice Z3 ["0", "schedule-truth.out"] 1
    val config = printer_config name [slice] (fn _ => ()) parser
    val root = OS.FileSys.tmpName ()
    val cache = join root "cache"
    val _ = remove_tree root
    val _ = mkdir root
    val options = fixture_options [Z3] 1 1 5 1 true cache NONE
    fun spawns_of_run () =
      let
        val _ = hhProver.reset_spawn_count ()
        val (result, _) = run_schedule options
      in
        (result, hhProver.spawn_count ())
      end
    val ((first, first_spawns), (second, second_spawns)) =
      with_fixtures [(Z3, config)] (fn () =>
        (spawns_of_run (), spawns_of_run ()))
    val first_cached = map #4 (#slices_run first)
    val second_cached = map #4 (#slices_run second)
    val _ = expect "scheduler cache hit spawns no processes"
      (#stopped first = hhSchedule.MaxProofs andalso first_spawns > 0 andalso
       List.all not first_cached andalso
       #stopped second = hhSchedule.MaxProofs andalso
       length (#suggestions second) = 1 andalso
       List.all (fn cached => cached) second_cached andalso
       second_spawns = 0)
    val _ = remove_tree root
  in
    ()
  end

fun await_schedule_test message ready =
  let
    val deadline = Time.+ (Time.now (), Time.fromSeconds 10)
    fun loop () =
      if ready () then ()
      else if Time.compare (Time.now (), deadline) <> LESS then
        raise Fail message
      else (OS.Process.sleep (Time.fromMilliseconds 10); loop ())
  in
    loop ()
  end

fun test_schedule_cancelled_cache parser =
  let
    val name = "hh-schedule-cancelled-cache"
    val slice = fixture_slice Z3 ["1", "e-gave-up.out"] 1
    val root = hhSchedule.new_problem_dir (hhConfig.state_dir ())
    val options = fixture_options [Z3] 1 1 5 1 true root NONE
    val config = printer_config name [slice] (fn _ => ()) parser
    val _ = ignore (hhProver.probe config)
  in
    with_fixtures [(Z3, config)] (fn () =>
  let
    val result = ref NONE
    val _ = hhProver.reset_spawn_count ()
    val thread = Thread.fork
      (fn () => result := SOME (#1 (run_schedule options)), [])
    val _ = await_schedule_test "cancelled slice never started"
      (fn () => hhProver.spawn_count () > 0)
    val _ = OS.Process.sleep (Time.fromMilliseconds 200)
    val _ = Thread.interrupt thread
    val _ = await_schedule_test "interrupted scheduler did not finish"
      (fn () => not (Thread.isActive thread))
    val _ = expect "scheduler interrupt cancels the running slice"
      (case !result of
           SOME value => #stopped value = hhSchedule.Interrupted
         | NONE => false)
    val _ = hhProver.reset_spawn_count ()
    val (retry, _) = run_schedule options
    val _ = expect "cancelled slices retry instead of caching a timeout"
      (hhProver.spawn_count () = 1 andalso
       case #slices_run retry of
           [(_, hhProver.SzsGaveUp, _, false)] => true
         | _ => false)
    val _ = hhProver.reset_spawn_count ()
    val (cached, _) = run_schedule options
  in
    expect "completed retry remains cacheable"
      (hhProver.spawn_count () = 0 andalso
       List.all #4 (#slices_run cached))
  end);
    remove_tree root
  end

fun test_schedule_isolation parser =
  let
    val name = "hh-schedule-isolation"
    val slice = fixture_slice Z3 ["0", "e-gave-up.out"] 1
    val mutex = Mutex.mutex ()
    fun locked action = hhProver.with_mutex mutex action
    val first_path = ref NONE
    val second_path = ref NONE
    val first_text = ref ""
    val second_text = ref ""
    val release = ref false
    val intact = ref false
    fun note (request : hhProver.run_request) =
      let
        val path = #problem request
        val first = locked (fn () =>
          case !first_path of
              NONE => (first_path := SOME path; true)
            | SOME _ => (second_path := SOME path; false))
      in
        if first then
          (first_text := String.concat (read_lines path);
           await_schedule_test "overlapping export did not finish"
             (fn () => locked (fn () => !release));
           intact := !first_text = String.concat (read_lines path))
        else second_text := String.concat (read_lines path)
      end
    val options = fixture_options [Z3] 1 1 5 1 false "" NONE
    val first_result = ref NONE
    fun overlapping_runs () =
      let
        val thread = Thread.fork
          (fn () => first_result := SOME (#1 (run_schedule options)), [])
        val _ = await_schedule_test "first export did not reach the prover"
          (fn () => locked (fn () => Option.isSome (!first_path)))
        val (second_result, _) = run_schedule_on ([], boolSyntax.F) options
        val _ = locked (fn () => release := true)
        val _ = await_schedule_test "first scheduler did not finish"
          (fn () => not (Thread.isActive thread))
      in
        second_result
      end
    val second_result =
      with_fixtures [(Z3, printer_config name [slice] note parser)]
        overlapping_runs
    val _ = expect "overlapping schedulers preserve their own prover inputs"
      (!first_path <> !second_path andalso !intact andalso
       !second_text <> "" andalso !first_text <> !second_text
       andalso Option.isSome (!first_result) andalso
       #stopped second_result = hhSchedule.Exhausted)
    val roots = map (OS.Path.dir o OS.Path.dir o valOf)
      [!first_path, !second_path]
  in
    expect "overlapping schedulers each remove only their own root"
      (not (List.exists is_dir roots) andalso is_dir (OS.Path.dir (hd roots)))
  end

fun test_schedule_timeout parser =
  let
    val name = "hh-schedule-timeout"
    val debug = OS.FileSys.tmpName ()
    val _ = remove_tree debug
    val options = fixture_options [Z3] 1 1 1 1 false "" (SOME debug)
    val (result, events) =
      with_fixtures [(Z3, sleeper_config Z3 name parser)] (fn () =>
        run_schedule options)
    val child_gone = fixture_child_gone debug name
    val _ = expect "scheduler timeout stop reason is reachable"
      (#stopped result = hhSchedule.Timeout andalso
       null (#suggestions result) andalso #t_total result < 7.0 andalso
       child_gone andalso schedule_events_sane events)
    val _ = remove_tree debug
  in
    ()
  end

fun test_schedule_filter_rankings parser =
  let
    val root = hhSchedule.new_problem_dir (hhConfig.state_dir ())
    val name = "hh-schedule-filter-rankings"
    val knn = ranking_fixture_slice Z3 "knn" 1
    val mepo = ranking_fixture_slice Z3 "mepo" 1
    val slices = [knn, mepo]
    val config = printer_config name slices (fn _ => ()) parser
    val options : hhConfig.hh_options =
      {timeout = 5, max_proofs = 1, provers = [Z3], slices = 2,
       cores = 1,
       export_workers = 1,
       filter = "", max_facts = NONE, format = "",
       type_enc = "", lam_trans = "", mono_iters = 3,
       mono_instances = NONE, minimize = true, preplay_timeout = 1.0,
       minimize_timeout = 1.0, cache = false, cache_dir = "",
       cache_max_entries = 100, debug_dir = NONE,
       preplay_drop_one = false, verbose = false}
    val knn_path = hhSchedule.problem_path root knn
    val mepo_path = hhSchedule.problem_path root mepo
    fun clean () = List.app (remove_tree o OS.Path.dir)
      [knn_path, mepo_path]
    val _ = clean ()
    fun run_with rankings = with_fixtures [(Z3, config)] (fn () =>
      hhSchedule.run_in root
        {options = options, goal = ([], boolSyntax.T), rankings = rankings,
         progress = NONE})
    val missing =
      ((ignore (run_with [("knn", ["boolTheory.TRUTH"])]); false)
       handle Fail message =>
         contains "missing premise ranking" message)
    val _ = expect "scheduler rejects a missing filter ranking before export"
      (missing andalso
       not (OS.FileSys.access (knn_path, [])) andalso
       not (OS.FileSys.access (mepo_path, [])))
      handle OS.SysErr _ => OK ()
    val result =
      run_with
        [("knn", ["boolTheory.TRUTH"]), ("mepo", ["boolTheory.T_DEF"])]
    val knn_text = String.concat (read_lines knn_path)
    val mepo_text = String.concat (read_lines mepo_path)
    val _ = expect "filter-only problem keys and directories are distinct"
      (knn_path <> mepo_path andalso
       OS.FileSys.access (knn_path, []) andalso
       OS.FileSys.access (mepo_path, []))
    val _ = expect "mixed-filter schedules route their own rankings"
      (#stopped result = hhSchedule.Exhausted andalso
       length (#slices_run result) = 2 andalso knn_text <> mepo_text)
    val _ = clean ()
  in
    remove_tree root
  end

fun test_schedule_knn_anchor_export () =
  let
    val root = hhSchedule.new_problem_dir (hhConfig.state_dir ())
    val e = prover Eprover
    fun slice nfacts : hhProver.slice =
      {prover = Eprover, format = "fof", type_enc = "", lam_trans = "",
       nfacts = nfacts, filter = "knn", extra_opts = [], slice_size = 1}
    val one = slice 1
    val two = slice 2
    val schedule = [(e, one), (e, two)]
    val ranking = ["boolTheory.TRUTH", "boolTheory.T_DEF"]
    val options : hhConfig.hh_options =
      {timeout = 5, max_proofs = 1, provers = [Eprover], slices = 2,
       cores = 1,
       export_workers = 1,
       filter = "knn", max_facts = NONE, format = "",
       type_enc = "", lam_trans = "", mono_iters = 3,
       mono_instances = NONE, minimize = true, preplay_timeout = 1.0,
       minimize_timeout = 1.0, cache = false, cache_dir = "",
       cache_max_entries = 100, debug_dir = NONE,
       preplay_drop_one = false, verbose = false}
    val expected_one = OS.FileSys.tmpName ()
    val expected_two = OS.FileSys.tmpName ()
    val _ = List.app (fn path => OS.FileSys.remove path handle _ => ())
      [expected_one, expected_two]
    val _ = List.app mkdir [expected_one, expected_two]
    fun named count = smlRedirect.hidef mlThmData.thml_of_namel
      (List.take (ranking, count))
    val _ = hhExportFof.fof_export_pb expected_one
      (boolSyntax.T, named 1)
    val _ = hhExportFof.fof_export_pb expected_two
      (boolSyntax.T, named 2)
    val _ = List.app (remove_tree o OS.Path.dir)
      [hhSchedule.problem_path root one, hhSchedule.problem_path root two]
    val _ = hhSchedule.export_problems root options ([], boolSyntax.T)
      [("knn", ranking)] schedule
    val _ = expect "all-knn export preserves longest-ranking prefixes"
      (hhSchedule.problem_path root one <> hhSchedule.problem_path root two
       andalso
       String.concat (read_lines (hhSchedule.problem_path root one)) =
         String.concat (read_lines (join expected_one "atp_in")) andalso
       String.concat (read_lines (hhSchedule.problem_path root two)) =
         String.concat (read_lines (join expected_two "atp_in")))
    val _ = List.app remove_tree [expected_one, expected_two]
    val _ = List.app (remove_tree o OS.Path.dir)
      [hhSchedule.problem_path root one, hhSchedule.problem_path root two]
  in
    remove_tree root
  end

(* The monomorphiser makes about one instance per fact and drops a
   polymorphic fact that gets none, so a prover's instance cap below the
   slice's fact count used to cut the lowest-ranked facts. *)
fun test_schedule_mono_cap_export () =
  let
    val root = hhSchedule.new_problem_dir (hhConfig.state_dir ())
    val {name, exec_names, env_var, version_args, parse_version,
         tested_versions, supported_formats, mk_command, parse_output,
         slices, legacy, ...} = prover Eprover
    val small_cap : hhProver.prover_config =
      {name = name, exec_names = exec_names, env_var = env_var,
       version_args = version_args, parse_version = parse_version,
       tested_versions = tested_versions,
       supported_formats = supported_formats, mk_command = mk_command,
       parse_output = parse_output, mono_instances = 2, slices = slices,
       legacy = legacy}
    val facts = ["APPEND_NIL", "APPEND_ASSOC", "LENGTH_APPEND",
                 "REVERSE_APPEND"]
    val slice : hhProver.slice =
      {prover = Eprover, format = "tx0-", type_enc = "mono_native_fool",
       lam_trans = "lifting", nfacts = length facts, filter = "knn",
       extra_opts = [], slice_size = 1}
    val options : hhConfig.hh_options =
      {timeout = 5, max_proofs = 1, provers = [Eprover], slices = 1,
       cores = 1,
       export_workers = 1,
       filter = "knn", max_facts = NONE, format = "",
       type_enc = "", lam_trans = "", mono_iters = 3,
       mono_instances = NONE, minimize = true, preplay_timeout = 1.0,
       minimize_timeout = 1.0, cache = false, cache_dir = "",
       cache_max_entries = 100, debug_dir = NONE,
       preplay_drop_one = false, verbose = false}
    val goal = ([], ``LENGTH ([1] ++ [] ++ [2]) = LENGTH (REVERSE [1; 2n])``)
    val _ = smlRedirect.hidef (hhSchedule.export_problems root options goal
      [("knn", map (fn fact => "listTheory." ^ fact) facts)])
      [(small_cap, slice)]
    val problem =
      String.concat (read_lines (hhSchedule.problem_path root slice))
    fun exported fact =
      String.isSubstring ("thm_2ElistTheory_2E" ^
        String.translate (fn #"_" => "__" | c => str c) fact) problem
    val _ = expect "a prover's mono cap does not cut a slice's facts"
      (List.all exported facts)
  in
    remove_tree root
  end

fun test_with_problem_dir () =
  let
    val parent = OS.FileSys.tmpName ()
    val _ = OS.FileSys.remove parent
    val outside = OS.FileSys.tmpName ()
    val _ = OS.FileSys.remove outside
    val _ = mkdir outside
    val kept_file = join outside "kept"
    val _ = write_file kept_file "kept"
    fun options debug_dir =
      fixture_options [Eprover] 1 1 5 1 false "" debug_dir
    fun populate root =
      let
        val slice_dir = join root "e.knn.fof...32"
        val _ = mkdir slice_dir
        val _ = write_file (join slice_dir "atp_in") "fof(a, axiom, $true)."
        val _ = Posix.FileSys.symlink {old = outside, new = join root "link"}
      in
        root
      end
    val ok_root = hhSchedule.with_problem_dir parent (options NONE) populate
    val failed_root = ref ""
    val raised =
      (hhSchedule.with_problem_dir parent (options NONE)
         (fn root => (failed_root := populate root; raise Fail "boom"));
       false)
      handle Fail "boom" => true
    val debug_root =
      hhSchedule.with_problem_dir parent (options (SOME outside)) populate
    val roots = Array.array (4, "")
    val threads = List.tabulate (4, fn i =>
      Thread.fork (fn () =>
        Array.update (roots, i,
          hhSchedule.with_problem_dir parent (options NONE) populate), []))
    fun wait () =
      if List.exists Thread.isActive threads then
        (OS.Process.sleep (Time.fromMilliseconds 10); wait ())
      else ()
    val _ = wait ()
    val thread_roots = Array.foldr (op ::) [] roots
    fun distinct [] = true
      | distinct (x :: xs) = not (List.exists (fn y => y = x) xs) andalso
                             distinct xs
    val _ = expect "with_problem_dir removes its root after success"
      (not (is_dir ok_root) andalso is_dir parent)
    val _ = expect "with_problem_dir removes its root when the call raises"
      (raised andalso !failed_root <> "" andalso not (is_dir (!failed_root)))
    val _ = expect "with_problem_dir keeps its root in debug_dir"
      (is_dir debug_root andalso
       OS.Path.dir debug_root = join outside "problems")
    val _ = expect "remove_tree does not follow symbolic links"
      (OS.FileSys.access (kept_file, []))
    val _ = expect "concurrent with_problem_dir calls use and remove own roots"
      (List.all (fn root => root <> "" andalso not (is_dir root))
         thread_roots andalso
       distinct (ok_root :: debug_root :: thread_roots))
  in
    (* The selftest's own remove_tree follows symbolic links. *)
    List.app hhConfig.remove_tree [parent, outside]
  end

fun test_schedule_export_wiring () =
  let
    val root = hhSchedule.new_problem_dir (hhConfig.state_dir ())
    val e = prover Eprover
    val vampire = prover Vampire
    fun options mono_instances : hhConfig.hh_options =
      {timeout = 30, max_proofs = 1, provers = [Eprover], slices = 1,
       cores = 1,
       export_workers = 1,
       filter = "none", max_facts = NONE, format = "", type_enc = "",
       lam_trans = "", mono_iters = 3, mono_instances = mono_instances,
       minimize = true, preplay_timeout = 1.0, minimize_timeout = 1.0,
       cache = false, cache_dir = "", cache_max_entries = 100,
       debug_dir = NONE,
       preplay_drop_one = false, verbose = false}
    fun slice type_enc lam_trans : hhProver.slice =
      {prover = Eprover, format = "fof", type_enc = type_enc,
       lam_trans = lam_trans, nfacts = 0, filter = "none",
       extra_opts = [], slice_size = 1}
    val legacy = slice "" ""
    val lifting = slice "mono_guards" "lifting"
    val combs = slice "mono_guards" "combs"
    val goal = ([], boolSyntax.T)
    val legacy_path = hhSchedule.problem_path root legacy
    val lifting_path = hhSchedule.problem_path root lifting
    val combs_path = hhSchedule.problem_path root combs
    val _ = List.app (remove_tree o OS.Path.dir)
      [legacy_path, lifting_path, combs_path]
    val expected_dir = OS.FileSys.tmpName ()
    val _ = OS.FileSys.remove expected_dir
    val _ = mkdir expected_dir
    val _ = hhExportFof.fof_export_pb expected_dir (boolSyntax.T, [])
    val _ = hhSchedule.export_problems root (options NONE) goal
      [("none", [])] [(e, legacy)]
    val legacy_empty_text = String.concat (read_lines legacy_path)
    val _ = expect "legacy scheduler dispatch is byte-identical"
      (legacy_empty_text =
       String.concat (read_lines (join expected_dir "atp_in")))
    val _ = hhSchedule.export_problems root (options NONE) goal
      [("none", ["boolTheory.TRUTH"])] [(e, legacy)]
    val _ = expect "filter=none exports premises beyond the slice fact count"
      (legacy_empty_text <> String.concat (read_lines legacy_path))
    val _ = hhSchedule.export_problems root (options NONE) goal [("none", [])]
      [(e, lifting), (e, combs), (e, lifting)]
    val lifting_text = String.concat (read_lines lifting_path)
    val _ = expect "problem exports re-key full triples"
      (lifting_path <> combs_path andalso OS.FileSys.access (lifting_path, [])
       andalso OS.FileSys.access (combs_path, []))
    val _ = expect "nonlegacy triple dispatches to hhProblemGen"
      (contains "generated by hhProblemGen" lifting_text)
    val _ = expect "prover config mono-instance cap wins over default"
      (contains "mono_instances=128" lifting_text)
    val _ = hhSchedule.export_problems root
      (options (SOME 77)) goal [("none", [])] [(e, lifting)]
    val _ = expect "explicit mono-instance option beats the prover config cap"
      (contains "mono_instances=77" (String.concat (read_lines lifting_path)))
    fun mono_slice prover : hhProver.slice =
      {prover = prover, format = "th0", type_enc = "mono_native_higher",
       lam_trans = "keep_lams", nfacts = 0, filter = "none",
       extra_opts = [], slice_size = 1}
    val e_mono = mono_slice Eprover
    val vampire_mono = mono_slice Vampire
    val _ = hhSchedule.export_problems root (options NONE) goal [("none", [])]
      [(e, e_mono), (vampire, vampire_mono)]
    val e_mono_path = hhSchedule.problem_path root e_mono
    val vampire_mono_path = hhSchedule.problem_path root vampire_mono
    val _ = expect "prover-specific monomorphization exports stay distinct"
      (e_mono_path <> vampire_mono_path andalso
       contains "mono_instances=128"
         (String.concat (read_lines e_mono_path)) andalso
       contains "mono_instances=256"
         (String.concat (read_lines vampire_mono_path)))
    val _ = remove_tree expected_dir
  in
    remove_tree root
  end

fun list_directory directory =
  let
    val stream = OS.FileSys.openDir directory
    fun loop acc =
      case OS.FileSys.readDir stream of
          NONE => acc
        | SOME entry => loop (entry :: acc)
    val entries = loop []
      handle error => (OS.FileSys.closeDir stream; raise error)
  in
    OS.FileSys.closeDir stream;
    Portable.sort (fn a => fn b => String.compare (a, b) <> GREATER) entries
  end

fun test_schedule_legacy_sharing () =
  let
    val root = hhSchedule.new_problem_dir (hhConfig.state_dir ())
    val e = prover Eprover
    val vampire = prover Vampire
    fun options max_facts : hhConfig.hh_options =
      {timeout = 30, max_proofs = 1, provers = [Eprover], slices = 1,
       cores = 1,
       export_workers = 1,
       filter = "none", max_facts = max_facts, format = "",
       type_enc = "", lam_trans = "", mono_iters = 3, mono_instances = NONE,
       minimize = true, preplay_timeout = 1.0, minimize_timeout = 1.0,
       cache = false, cache_dir = "", cache_max_entries = 100,
       debug_dir = NONE, preplay_drop_one = false, verbose = false}
    fun slice prover filter nfacts : hhProver.slice =
      {prover = prover, format = "fof", type_enc = "", lam_trans = "",
       nfacts = nfacts, filter = filter, extra_opts = [], slice_size = 1}
    fun names facts = map (fn fact => "listTheory." ^ fact) facts
    val ranking = names ["APPEND_NIL", "APPEND_ASSOC", "LENGTH_APPEND",
                         "REVERSE_APPEND"]
    val other_ranking = rev ranking
    val goal = ([], boolSyntax.T)
    val generated = ref 0
    val copied = ref 0
    val copy_bytes = ref 0
    val observer : hhSchedule.export_observer =
      {generated = fn _ => generated := !generated + 1,
       copied = fn (_, bytes) =>
         (copied := !copied + 1; copy_bytes := !copy_bytes + bytes)}
    fun run options rankings schedule =
      (generated := 0; copied := 0; copy_bytes := 0;
       smlRedirect.hidef (hhSchedule.export_problems_observed observer root
         options goal rankings) schedule)
    fun text slice =
      String.concat (read_lines (hhSchedule.problem_path root slice))
    fun direct ranking count =
      let
        val dir = OS.FileSys.tmpName ()
        val _ = OS.FileSys.remove dir
        val _ = mkdir dir
        val named = smlRedirect.hidef mlThmData.thml_of_namel
          (aiLib.first_n count ranking)
        val _ = hhExportFof.fof_export_pb dir
          (boolSyntax.list_mk_imp goal,
           List.filter (null o Thm.hyp o #2) named)
        val result = String.concat (read_lines (join dir "atp_in"))
      in
        (remove_tree dir; result)
      end
    (* kNN occurs under several slice keys, one selection (length 4). *)
    val knn_a = slice Eprover "knn" 3
    val knn_b = slice Vampire "knn" 3
    val knn_c = slice Eprover "knn" 4
    val knn_long = slice Vampire "knn" 100
    val mepo = slice Eprover "mepo" 4
    val _ = run (options NONE) [("knn", ranking), ("mepo", other_ranking)]
      [(e, knn_a), (vampire, knn_b), (e, knn_c), (vampire, knn_long),
       (e, mepo)]
    val _ = expect "legacy problems with one selection are generated once"
      (!generated = 3 andalso !copied = 2 andalso !copy_bytes > 0)
    val _ = expect "equal-length selections of different filters stay apart"
      (text knn_c <> text mepo andalso
       text mepo = direct other_ranking 4)
    val _ = expect "copied legacy bytes equal a direct export"
      (text knn_c = direct ranking 4 andalso text knn_long = text knn_c andalso
       text knn_a = direct ranking 3 andalso text knn_b = text knn_a andalso
       text knn_a <> text knn_c)
    val _ = expect "copies are separate files at their own paths"
      (hhSchedule.problem_path root knn_a <>
       hhSchedule.problem_path root knn_b andalso
       OS.FileSys.fileSize (hhSchedule.problem_path root knn_b) =
         Position.fromInt (String.size (text knn_a)))
    (* filter none: the whole ranking, up to the optional cap. *)
    val none_a = slice Eprover "none" 0
    val none_b = slice Vampire "none" 7
    val _ = run (options NONE) [("none", ranking)]
      [(e, none_a), (vampire, none_b)]
    val _ = expect "filter none shares the whole ranking"
      (!generated = 1 andalso !copied = 1 andalso
       text none_a = direct ranking 4 andalso text none_b = text none_a)
    val _ = run (options (SOME 2)) [("none", ranking)]
      [(e, none_a), (vampire, none_b)]
    val _ = expect "filter none honours max_facts and still shares"
      (!generated = 1 andalso !copied = 1 andalso
       text none_a = direct ranking 2 andalso text none_b = text none_a)
    (* A retry on the same root re-exports one former duplicate. *)
    val _ = run (options NONE) [("knn", ranking)]
      [(e, knn_a), (vampire, knn_b)]
    val before_a = text knn_a
    val _ = run (options NONE) [("knn", other_ranking)] [(vampire, knn_b)]
    val _ = expect "a retry changes one former duplicate only"
      (!generated = 1 andalso !copied = 0 andalso
       text knn_a = before_a andalso
       text knn_b = direct other_ranking 3 andalso text knn_a <> text knn_b)
    val _ = run (options NONE) [("knn", other_ranking)]
      [(e, knn_a), (vampire, knn_b)]
    val _ = expect "a retry re-copies over the former duplicate"
      (!generated = 1 andalso !copied = 1 andalso
       text knn_a = text knn_b andalso
       text knn_a = direct other_ranking 3)
    (* A failed copy leaves neither a temporary nor a changed target. *)
    val source = hhSchedule.problem_path root knn_a
    val parent = join root "copy_failure"
    val _ = mkdir parent
    val blocked = join parent "atp_in"
    val _ = mkdir blocked
    val _ = write_file (join blocked "occupied") "x"
    val raised = (hhSchedule.copy_file source blocked; false)
      handle OS.SysErr _ => true
    val missing = join (join parent "absent") "atp_in"
    val raised_missing = (hhSchedule.copy_file source missing; false)
      handle IO.Io _ => true
    val good = join parent "good"
    val _ = write_file good "old"
    val size = hhSchedule.copy_file source good
    val _ = expect "a failed copy raises and leaves no temporary file"
      (raised andalso raised_missing andalso
       is_dir blocked andalso
       list_directory parent = ["atp_in", "good"] andalso
       size = String.size (text knn_a) andalso
       String.concat (read_lines good) = text knn_a)
    (* A writer that fails midway leaves the old target and no temporary. *)
    val failed = (hhConfig.write_atomically
      {open_out = TextIO.openOut, close_out = TextIO.closeOut} good
      (fn out => (TextIO.output (out, "partial"); raise Div)); false)
      handle Div => true
    val _ = expect "a failing atomic writer keeps the target and cleans up"
      (failed andalso list_directory parent = ["atp_in", "good"] andalso
       String.concat (read_lines good) = text knn_a)
  in
    remove_tree root
  end

fun test_hhSchedule () =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      SOME _ => ()
    | NONE =>
        let
          val parser = #parse_output (prover Eprover)
          val started = Time.now ()
          val _ = test_schedule_max_proofs parser
          val _ = test_schedule_reconstruction_failure parser
          val _ = test_schedule_without_minimization ()
          val _ = test_schedule_failed_list_once ()
          val _ = test_schedule_drop_one ()
          val _ = test_schedule_early_stop parser
          val _ = test_schedule_budget_truncation parser
          val _ = test_schedule_cache parser
          val _ = test_schedule_cancelled_cache parser
          val _ = test_schedule_isolation parser
          val _ = test_schedule_timeout parser
          val _ = test_schedule_filter_rankings parser
        in
          expect "scheduler hermetic suite stays within its wall-time bound"
            (Time.toReal (Time.- (Time.now (), started)) < 60.0)
        end

structure StagedFixture =
struct
  val e = prover Eprover
  val vampire = prover Vampire
  fun options_capped cores workers debug max_facts cap : hhConfig.hh_options =
    {timeout = 30, max_proofs = 1, provers = [Eprover], slices = 1,
     cores = cores,
     export_workers = workers,
     filter = "none", max_facts = max_facts, format = "",
     type_enc = "", lam_trans = "", mono_iters = 3, mono_instances = cap,
     minimize = true, preplay_timeout = 1.0, minimize_timeout = 1.0,
     cache = false, cache_dir = "", cache_max_entries = 100,
     debug_dir = debug, preplay_drop_one = false, verbose = false}
  fun options_with cores workers debug max_facts =
    options_capped cores workers debug max_facts NONE
  fun legacy prover filter nfacts : hhProver.slice =
    {prover = prover, format = "fof", type_enc = "", lam_trans = "",
     nfacts = nfacts, filter = filter, extra_opts = [], slice_size = 1}
  fun generated prover filter nfacts : hhProver.slice =
    {prover = prover, format = "tx0-", type_enc = "mono_native_fool",
     lam_trans = "lifting", nfacts = nfacts, filter = filter,
     extra_opts = [], slice_size = 1}
  val ranking = map (fn fact => "listTheory." ^ fact)
    ["APPEND_NIL", "APPEND_ASSOC", "LENGTH_APPEND"]
  val bad_ranking = ranking @ ["listTheory.NO_SUCH_THEOREM"]
  val goal : Term.term list * Term.term =
    ([], ``LENGTH ([1] ++ [] ++ [2]) = 3n``)
  fun quiet f = smlRedirect.hidef f ()
  fun root_files root =
    List.concat (map (fn directory =>
      map (fn name => join directory name)
        (list_directory (join root directory)))
      (list_directory root))
  fun sorted_files root =
    Portable.sort (fn a => fn b => String.compare (a, b) <> GREATER)
      (root_files root)
  (* The files of a root (relative paths) with their bytes, sorted. *)
  fun tree root =
    map (fn file => (file, String.concat (read_lines (join root file))))
      (sorted_files root)
  (* A start whose runs stay below the next power of ten (the counter
     only moves forward, so a fresh start is the next number unless a
     power of ten is near). *)
  fun quiet_start () =
    let
      val now = counter ()
      val next = power_above now
    in
      if next - now > 5000 then now + 1 else next + 10
    end
end

fun test_schedule_staged () =
  let
    open StagedFixture
    fun options max_facts = options_with 1 1 NONE max_facts
    (* The ordered work description. *)
    val root = hhSchedule.new_problem_dir (hhConfig.state_dir ())
    val schedule =
      [(e, legacy Eprover "knn" 2), (vampire, legacy Vampire "knn" 2),
       (e, generated Eprover "knn" 2), (e, legacy Eprover "knn" 3),
       (vampire, legacy Vampire "knn" 100), (e, generated Eprover "knn" 3)]
    val work = hhSchedule.ordered_work root (options NONE)
      [("knn", ranking)] schedule
    fun path_of (_, slice) = hhSchedule.problem_path root slice
    val first = path_of (hd schedule)
    val fourth = path_of (List.nth (schedule, 3))
    val _ = expect "work follows the schedule with index, path and key"
      (map #index work = [0, 1, 2, 3, 4, 5] andalso
       map #path work = map path_of schedule andalso
       map #key work =
         [("knn", 2), ("knn", 2), ("knn", 2), ("knn", 3), ("knn", 3),
          ("knn", 3)])
    val _ = expect "work kinds mark legacy sharing and generated jobs"
      (case map #kind work of
           [hhSchedule.ExportLegacy, hhSchedule.CopyLegacy one,
            hhSchedule.ExportGenerated g1, hhSchedule.ExportLegacy,
            hhSchedule.CopyLegacy two, hhSchedule.ExportGenerated g2] =>
             one = first andalso two = fourth andalso
             #mono_instances g1 = Int.max (#mono_instances e, 2) andalso
             #mono_instances g2 = Int.max (#mono_instances e, 3) andalso
             #mono_iters g1 = 3
         | _ => false)
    val _ = expect "ordered_work rejects a missing ranking"
      ((hhSchedule.ordered_work root (options NONE) [] schedule; false)
       handle Fail _ => true)
    val _ = expect "export_problems rejects a missing ranking up front"
      (((quiet (fn () => hhSchedule.export_problems root (options NONE)
          goal [] schedule)); false) handle Fail _ => true andalso
       null (list_directory root))
    (* run_staged over fake stages: failures at every stage and index.
       failing lists the (stage, index) pairs that raise; boom builds the
       exception. *)
    datatype stage = Prepare | Finish | Publish
    fun scenario_with boom window failing =
      let
        val log = ref []
        val published = ref []
        fun note s = log := s :: !log
        fun name word i = word ^ " " ^ Int.toString i
        fun hit stage i = List.exists (fn f => f = (stage, i)) failing
        fun prepare i =
          (note (name "prepare" i);
           if hit Prepare i then raise boom (name "prepare" i) else i)
        fun submit (_, i) = (note (name "submit" i); i)
        fun await i =
          (note (name "finish" i);
           if hit Finish i then raise boom (name "finish" i) else i)
        fun publish (_, i) =
          (note (name "publish" i);
           if hit Publish i then raise boom (name "publish" i)
           else published := i :: !published)
        fun abandon i = note (name "abandon" i)
        fun release i = note (name "release" i)
        val outcome = (hhSchedule.run_staged {window = window}
          {prepare = prepare, submit = submit, await = await,
           publish = publish, abandon = abandon, release = release}
          [0, 1, 2, 3, 4, 5]; "ok")
          handle Fail message => message
               | Interrupt => "interrupt"
      in
        (outcome, rev (!published), rev (!log))
      end
    fun scenario window failing =
      scenario_with (fn message => Fail message) window failing
    fun numbered word log =
      List.mapPartial (fn s => if String.isPrefix (word ^ " ") s then
        SOME (valOf (Int.fromString
          (String.extract (s, String.size word + 1, NONE))))
        else NONE) log
    val (ok0, pub0, log0) = scenario 0 []
    val _ = expect "staged export publishes everything in order"
      (ok0 = "ok" andalso pub0 = [0, 1, 2, 3, 4, 5] andalso
       numbered "prepare" log0 = [0, 1, 2, 3, 4, 5])
    val _ = expect "window 0 resolves each item before preparing the next"
      (List.take (log0, 6) =
         ["prepare 0", "submit 0", "finish 0", "publish 0",
          "prepare 1", "submit 1"])
    val (ok3, pub3, log3) = scenario 3 []
    val _ = expect "a window submits at admission and awaits at resolution"
      (ok3 = "ok" andalso pub3 = [0, 1, 2, 3, 4, 5] andalso
       List.take (log3, 9) =
         ["prepare 0", "submit 0", "prepare 1", "submit 1", "prepare 2",
          "submit 2", "prepare 3", "submit 3", "finish 0"])
    fun check message window failing error prefix =
      let val (outcome, pub, _) = scenario window failing in
        expect message (outcome = error andalso pub = prefix)
      end
    val _ = check "prepare failure: earlier work is published" 0
      [(Prepare, 3)] "prepare 3" [0, 1, 2]
    val _ = check "prepare failure with a window publishes the prefix" 3
      [(Prepare, 4)] "prepare 4" [0, 1, 2, 3]
    val _ = check "finish failure raises its index and publishes the prefix"
      0 [(Finish, 2)] "finish 2" [0, 1]
    val _ = check "publish failure raises its index and publishes the prefix"
      0 [(Publish, 1)] "publish 1" [0]
    val _ = check "a windowed finish failure drops later work" 3
      [(Finish, 1)] "finish 1" [0]
    val _ = check "a windowed publish failure is earliest" 3
      [(Publish, 0)] "publish 0" []
    val _ = check "an earlier finish failure beats a later prepare failure" 3
      [(Prepare, 4), (Finish, 2)] "finish 2" [0, 1]
    val _ = check "an earlier publish failure beats a later prepare failure"
      3 [(Prepare, 2), (Publish, 1)] "publish 1" [0]
    val _ = check "an earlier finish failure beats a later publish failure"
      3 [(Publish, 3), (Finish, 1)] "finish 1" [0]
    val (_, pub_two, log_two) = scenario 3 [(Prepare, 4), (Finish, 2)]
    val _ = expect "two failures: later work is abandoned newest first"
      (List.filter (String.isPrefix "abandon") log_two =
         ["abandon 3", "abandon 2"] andalso not (List.exists
           (fn i => i >= 2) pub_two) andalso
       not (List.exists (fn s => s = "prepare 5" orelse s = "finish 3")
         log_two))
    val (_, _, windowed) = scenario 3 [(Finish, 1)]
    val _ = expect "after a failure later work is abandoned, newest first"
      (List.filter (String.isPrefix "abandon") windowed =
         ["abandon 4", "abandon 3", "abandon 2", "abandon 1"] andalso
       not (List.exists (fn s => s = "prepare 5") windowed))
    val (_, _, immediate) = scenario 0 [(Finish, 2)]
    val _ = expect "no work is admitted after a failure"
      (numbered "prepare" immediate = [0, 1, 2])
    val (_, _, drained) = scenario 3 [(Prepare, 4)]
    val _ = expect "a prepare failure resolves the earlier indices first"
      (numbered "publish" drained = [0, 1, 2, 3] andalso
       numbered "prepare" drained = [0, 1, 2, 3, 4])
    val (_, _, failed_publish) = scenario 0 [(Publish, 1)]
    val _ = expect "a failed publish releases what it was given"
      (List.filter (String.isPrefix "release") failed_publish = ["release 1"]
       andalso List.exists (fn s => s = "abandon 1") failed_publish)
    fun interrupted window failing =
      scenario_with (fn _ => Interrupt) window failing
    val (outcome, pub, log) = interrupted 3 [(Finish, 2)]
    val _ = expect "an interrupt propagates and abandons the waiting work"
      (outcome = "interrupt" andalso pub = [0, 1] andalso
       List.filter (String.isPrefix "abandon") log =
         ["abandon 5", "abandon 4", "abandon 3", "abandon 2"] andalso
       numbered "prepare" log = [0, 1, 2, 3, 4, 5])
    val (outcome, pub, log) = interrupted 3 [(Prepare, 4)]
    val _ = expect "an interrupt in prepare abandons the waiting work"
      (outcome = "interrupt" andalso pub = [0] andalso
       List.filter (String.isPrefix "abandon") log =
         ["abandon 3", "abandon 2", "abandon 1"])
    (* The real stages: a fetch failure at a later index. *)
    val bad_rank = [("knn", bad_ranking)]
    val failing = [(e, legacy Eprover "knn" 2), (e, generated Eprover "knn" 2),
                   (vampire, generated Vampire "knn" 4),
                   (vampire, legacy Vampire "knn" 4)]
    val raised = (quiet (fn () => hhSchedule.export_problems root
      (options NONE) goal bad_rank failing); false)
      handle Feedback.HOL_ERR _ => true
    val _ = expect "a fetch failure publishes the prefix and nothing else"
      (raised andalso
       List.all (fn (_, slice) => not (OS.FileSys.access
         (hhSchedule.problem_path root slice, []))) (List.drop (failing, 2))
       andalso OS.FileSys.access
         (hhSchedule.problem_path root (#2 (hd failing)), [])
       andalso OS.FileSys.access
         (hhSchedule.problem_path root (#2 (hd (tl failing))), [])
       andalso List.all (not o String.isSuffix ".tmp") (root_files root))
    val _ = remove_tree root
    (* A publish failure at a later index: the final path of the third
       problem is a non-empty directory, so its commit fails. *)
    val root = hhSchedule.new_problem_dir (hhConfig.state_dir ())
    val blocked = hhSchedule.problem_path root (#2 (List.nth (failing, 2)))
    val _ = hhConfig.ensure_dir (OS.Path.dir blocked)
    val _ = mkdir blocked
    val _ = write_file (join blocked "occupied") "x"
    val raised = (quiet (fn () => hhSchedule.export_problems root
      (options NONE) goal [("knn", ranking)] failing); false)
      handle OS.SysErr _ => true
    val _ = expect "a failing commit publishes the prefix and leaves no temp"
      (raised andalso
       OS.FileSys.access
         (hhSchedule.problem_path root (#2 (hd failing)), []) andalso
       OS.FileSys.access
         (hhSchedule.problem_path root (#2 (hd (tl failing))), []) andalso
       is_dir blocked andalso
       not (OS.FileSys.access (hhSchedule.problem_path root
         (#2 (List.nth (failing, 3))), [])) andalso
       List.all (not o String.isSuffix ".tmp") (root_files root))
    val _ = remove_tree root
    (* A legacy failure before the first write leaves no staging file. *)
    val root = hhSchedule.new_problem_dir (hhConfig.state_dir ())
    val raised = (quiet (fn () => hhSchedule.export_problems root
      (options NONE) ([], ``\x:num. x``) [("knn", ranking)]
      [(e, legacy Eprover "knn" 2)]); false) handle Feedback.HOL_ERR _ => true
    val _ = expect "a failing legacy export leaves no staged or final file"
      (raised andalso null (root_files root))
    val file = join root "direct"
    val raised_direct =
      (hhExportFof.fof_export_pbfile file (``\x:num. x``, []); false)
      handle Feedback.HOL_ERR _ => true
    val _ = expect "a direct legacy failure raises before the first write"
      (raised_direct andalso String.size (String.concat (read_lines file)) = 0)
    val _ = remove_tree root
    (* with_problem_dir removes the root, staged files included. *)
    val parent = hhSchedule.new_problem_dir (hhConfig.state_dir ())
    val seen = ref ""
    val raised = (hhSchedule.with_problem_dir parent (options NONE)
      (fn root =>
        (seen := root;
         quiet (fn () => hhSchedule.export_problems root (options NONE)
           goal bad_rank failing))); false) handle Feedback.HOL_ERR _ => true
    val _ = expect "with_problem_dir removes the root after a failed export"
      (raised andalso !seen <> "" andalso not (is_dir (!seen)) andalso
       null (list_directory parent))
  in
    remove_tree parent
  end

val _ = test_with_problem_dir ()
val _ = test_schedule_export_wiring ()
val _ = test_schedule_legacy_sharing ()
val _ = test_schedule_staged ()

(* Bounded waiting without sleeps: a monitor is a mutex and a condition
   variable.  monitor_do runs f with the mutex held and wakes the waiters;
   monitor_until waits for a predicate (evaluated with the mutex held) and
   fails after a limit, so that a broken test cannot hang. *)
type monitor = Mutex.mutex * ConditionVar.conditionVar

fun new_monitor () : monitor = (Mutex.mutex (), ConditionVar.conditionVar ())

fun monitor_do ((mutex, changed) : monitor) f =
  let
    val _ = Mutex.lock mutex
    val result = Exn.capture f ()
    val _ = ConditionVar.broadcast changed
    val _ = Mutex.unlock mutex
  in
    Exn.release result
  end

fun monitor_until ((mutex, changed) : monitor) message predicate =
  let
    val limit = Time.+ (Time.now (), Time.fromSeconds 30)
    fun loop () =
      if predicate () then ()
      else if Time.>= (Time.now (), limit) then raise Fail message
      else (ignore (ConditionVar.waitUntil (changed, mutex, limit)); loop ())
    val _ = Mutex.lock mutex
    val result = Exn.capture loop ()
    val _ = Mutex.unlock mutex
  in
    Exn.release result
  end

(* A fork that records its threads; wrap lets a test fail or count forks. *)
fun recording_fork wrap =
  let
    val threads = ref ([] : Thread.thread list)
    val lock = Mutex.mutex ()
    fun fork f =
      let val thread = wrap hhPool.default_fork f in
        (Mutex.lock lock; threads := thread :: !threads; Mutex.unlock lock;
         thread)
      end
    fun recorded () =
      let
        val _ = Mutex.lock lock
        val all = !threads
        val _ = Mutex.unlock lock
      in rev all end
  in
    (fork, recorded)
  end

(* Threads are not joinable: poll until none is active, up to a limit.  The
   polling orders nothing; it only waits for exits that already happened
   logically (the pool has accounted for them). *)
fun await_exits message threads =
  let
    val limit = Time.+ (Time.now (), Time.fromSeconds 30)
    fun loop () =
      if not (List.exists Thread.isActive (threads ())) then ()
      else if Time.>= (Time.now (), limit) then raise Fail message
      else (OS.Process.sleep (Time.fromMilliseconds 5); loop ())
  in loop () end

(* Every recorded thread has exited.  No polling: the pool joined them. *)
fun all_exited threads = not (List.exists Thread.isActive (threads ()))

fun test_hhPool () =
  let
    val gates = new_monitor ()
    val opened = ref ([] : int list)
    val started = ref ([] : int list)
    val finished = ref ([] : int list)
    val active = ref 0
    val most = ref 0
    val exited = ref ([] : int list)
    val wrote = ref ([] : int list)
    val discarded = ref ([] : int list)
    fun reset () =
      (opened := []; started := []; finished := []; active := 0; most := 0;
       exited := []; wrote := []; discarded := [])
    fun member list i = List.exists (fn j => j = i) list
    fun open_gate i = monitor_do gates (fn () => opened := i :: !opened)
    fun open_all n = List.app open_gate (List.tabulate (n, fn i => i))
    fun has_finished i () = member (!finished) i
    (* A job that waits at its gate (interruptibly), then yields i. *)
    fun job i =
      {run = fn () =>
         ((monitor_do gates (fn () =>
             (started := i :: !started; active := !active + 1;
              most := Int.max (!most, !active)));
           monitor_until gates "gate never opened"
             (fn () => member (!opened) i);
           monitor_do gates (fn () =>
             (wrote := i :: !wrote; finished := i :: !finished;
              active := !active - 1));
           i)
          handle exn =>
            (monitor_do gates (fn () =>
               (exited := i :: !exited; active := !active - 1));
             raise exn)),
       discard = fn () =>
         monitor_do gates (fn () => discarded := i :: !discarded)}
    fun in_thread f =
      let
        val result = ref NONE
        val thread = Thread.fork (fn () =>
          result := SOME (Exn.capture f ()), [])
      in (thread, result) end
    (* Bounded workers: two run, the others wait. *)
    val _ = reset ()
    val (fork, threads) = recording_fork (fn start => start)
    val (stats_full, values, stats_end) =
      hhPool.with_pool {workers = 2, fork = fork} (fn pool =>
        let
          val jobs = List.tabulate (5, fn i => hhPool.submit pool (job i))
          val _ = monitor_until gates "two workers did not start"
            (fn () => length (!started) = 2)
          val full = hhPool.stats pool
          val _ = open_all 5
          val values = map hhPool.await jobs
        in (full, values, hhPool.stats pool) end)
    val _ = expect "pool: running workers and waiting jobs are bounded"
      (#running stats_full = 2 andalso #waiting stats_full = 3 andalso
       #max_running stats_end = 2 andalso !most = 2 andalso
       length (!started) = 5 andalso length (threads ()) = 5)
    val _ = expect "pool: with_pool returns only after every worker exited"
      (all_exited threads)
    val _ = expect "pool: results come back in submission order"
      (values = [0, 1, 2, 3, 4])
    (* Out-of-order completion: await still delivers in order. *)
    val _ = reset ()
    val (fork, threads) = recording_fork (fn start => start)
    val completed = hhPool.with_pool {workers = 3, fork = fork} (fn pool =>
      let
        val jobs = List.tabulate (3, fn i => hhPool.submit pool (job i))
        val _ = monitor_until gates "three workers did not start"
          (fn () => length (!started) = 3)
        val _ = List.app (fn i =>
          (open_gate i; monitor_until gates "job did not finish"
             (has_finished i))) [2, 1, 0]
      in (rev (!finished), map hhPool.await jobs) end)
    val _ = expect "pool: out-of-order completion is awaited in order"
      (completed = ([2, 1, 0], [0, 1, 2]) andalso all_exited threads)
    (* An exception is recorded for the caller; discard follows it. *)
    val _ = reset ()
    val raised = hhPool.with_pool {workers = 2, fork = hhPool.default_fork}
      (fn pool =>
        let
          val bad = hhPool.submit pool
            {run = fn () => raise Fail "boom",
             discard = fn () => discarded := 7 :: !discarded}
          val good = hhPool.submit pool (job 1)
          val _ = open_gate 1
          val value = hhPool.await good
        in
          ((hhPool.await bad; "no exception") handle Fail message =>
             message ^ " " ^ Int.toString value)
        end)
    val _ = expect "pool: a job's exception reaches await, then discard runs"
      (raised = "boom 1" andalso member (!discarded) 7)
    (* Abandon: a waiting job never starts; a running job is interrupted,
       stopped, discarded once and writes nothing afterwards. *)
    val _ = reset ()
    val (fork, threads) = recording_fork (fn start => start)
    val _ = hhPool.with_pool {workers = 2, fork = fork} (fn pool =>
      let
        val running = hhPool.submit pool (job 0)
        val other = hhPool.submit pool (job 1)
        val waiting = hhPool.submit pool (job 2)
        val _ = monitor_until gates "workers did not start"
          (fn () => length (!started) = 2)
        val _ = hhPool.abandon waiting
        val _ = hhPool.abandon running
        val _ = expect "abandon: the worker stopped before abandon returned"
          (member (!exited) 0 andalso member (!discarded) 0 andalso
           member (!discarded) 2)
        val _ = hhPool.abandon running
        val _ = open_all 3
        val _ = hhPool.await other
      in () end)
    val _ = expect "abandon: cancelled jobs wrote nothing, discard repeats"
      (all_exited threads andalso not (member (!wrote) 0) andalso
       not (member (!started) 2) andalso !wrote = [1] andalso
       member (!discarded) 0 andalso
       length (threads ()) = 2)
    (* The caller is interrupted while it waits: the pool closes, the
       running job is interrupted and everything stops. *)
    val _ = reset ()
    val (fork, threads) = recording_fork (fn start => start)
    val (caller, outcome) = in_thread (fn () =>
      hhPool.with_pool {workers = 1, fork = fork} (fn pool =>
        hhPool.await (hhPool.submit pool (job 0))))
    val _ = monitor_until gates "job did not start"
      (fn () => member (!started) 0)
    val _ = Thread.interrupt caller
    val _ = monitor_until gates "caller did not stop"
      (fn () => member (!exited) 0)
    val _ = await_exits "caller did not exit" (fn () => [caller])
    val _ = expect "interrupt of the caller stops the worker and propagates"
      ((case !outcome of
            SOME (Exn.Exn Interrupt) => true
          | _ => false) andalso all_exited threads)
    val _ = expect "interrupt of the caller discards the job"
      (member (!discarded) 0 andalso not (member (!wrote) 0))
    (* A Ctrl-C (a broadcast interrupt) that arrives while the owner waits
       for a worker to stop is not lost: it is raised after the cleanup.  The
       job answers its own interrupt by broadcasting one, then returns. *)
    fun swallowing_job i =
      {run = fn () =>
         ((monitor_do gates (fn () => started := i :: !started);
           monitor_until gates "gate never opened"
             (fn () => member (!opened) i); i)
          handle Interrupt =>
            (Thread.broadcastInterrupt ();
             monitor_do gates (fn () => exited := i :: !exited); i)),
       discard = fn () =>
         monitor_do gates (fn () => discarded := i :: !discarded)}
    fun as_owner f =
      let
        val result = ref NONE
        val _ = Thread.fork (fn () =>
          (result := SOME (Exn.capture f ());
           monitor_do gates (fn () => ())),
          [Thread.EnableBroadcastInterrupt true,
           Thread.InterruptState Thread.InterruptAsynch])
      in
        (* The broadcast reaches every thread that accepts one: this one
           must not, or the test would interrupt the whole selftest. *)
        Thread_Attributes.with_attributes Thread_Attributes.private_interrupts
          (fn _ =>
             (monitor_until gates "owner did not finish"
                (fn () => isSome (!result));
              valOf (!result)))
      end
    val _ = reset ()
    val (fork, threads) = recording_fork (fn start => start)
    val closing = as_owner (fn () =>
      hhPool.with_pool {workers = 1, fork = fork} (fn pool =>
        let val job = hhPool.submit pool (swallowing_job 0) in
          monitor_until gates "job did not start"
            (fn () => member (!started) 0)
        end))
    val _ = expect "a Ctrl-C during close is raised after the cleanup"
      ((case closing of Exn.Exn Interrupt => true | _ => false) andalso
       member (!exited) 0 andalso member (!discarded) 0 andalso
       all_exited threads)
    val _ = reset ()
    val (fork, threads) = recording_fork (fn start => start)
    val abandoning = as_owner (fn () =>
      hhPool.with_pool {workers = 1, fork = fork} (fn pool =>
        let val job = hhPool.submit pool (swallowing_job 0) in
          monitor_until gates "job did not start"
            (fn () => member (!started) 0);
          ((hhPool.abandon job; "not interrupted")
           handle Interrupt =>
             (if member (!discarded) 0 then "interrupted, discarded"
              else "interrupted, not discarded"))
        end))
    val _ = expect "a Ctrl-C during abandon is raised after the discard"
      ((case abandoning of
            Exn.Res "interrupted, discarded" => true
          | _ => false) andalso member (!exited) 0 andalso
       all_exited threads)
    (* Partial launch: the third thread cannot be started. *)
    val _ = reset ()
    fun failing_at n =
      let val calls = ref 0 in
        fn start => fn f =>
          (calls := !calls + 1;
           if !calls = n then raise Fail "no thread" else start f)
      end
    val (fork, threads) = recording_fork (failing_at 3)
    val message = ((hhPool.with_pool {workers = 3, fork = fork} (fn pool =>
      let
        val a = hhPool.submit pool (job 0)
        val b = hhPool.submit pool (job 1)
        val _ = monitor_until gates "started"
          (fn () => length (!started) = 2)
        val c = hhPool.submit pool (job 2)
      in "launched" end)) handle Fail text => text)
    val _ = expect "partial launch: the failure propagates after the started \
      \workers stopped"
      (message = "no thread" andalso all_exited threads andalso
       length (!exited) = 2 andalso
       member (!discarded) 0 andalso member (!discarded) 1 andalso
       not (member (!discarded) 2) andalso null (!wrote))
    (* A thread that cannot be started for a waiting job fails that job. *)
    val _ = reset ()
    val (fork, threads) = recording_fork (failing_at 2)
    val message = hhPool.with_pool {workers = 1, fork = fork} (fn pool =>
      let
        val first = hhPool.submit pool (job 0)
        val second = hhPool.submit pool (job 1)
        val _ = open_all 2
        val value = hhPool.await first
      in
        ((hhPool.await second; "no exception") handle Fail text => text)
      end)
    val _ = expect "a failed hand-over fails the waiting job"
      (message = "no thread" andalso all_exited threads andalso
       member (!discarded) 1 andalso not (member (!started) 1))
    (* A closed pool admits nothing. *)
    val escaped = ref NONE
    val _ = hhPool.with_pool {workers = 1, fork = hhPool.default_fork}
      (fn pool => escaped := SOME pool)
    val _ = expect "a closed pool refuses jobs"
      ((hhPool.submit (valOf (!escaped)) (job 0); false)
       handle Fail _ => true)
    (* Two concurrent pools do not disturb each other. *)
    fun sum_in_pool seed =
      hhPool.with_pool {workers = 2, fork = hhPool.default_fork} (fn pool =>
        let
          val jobs = List.tabulate (6, fn i =>
            hhPool.submit pool {run = fn () => seed * 10 + i,
                                discard = fn () => ()})
        in map hhPool.await jobs end)
    val (t1, r1) = in_thread (fn () => sum_in_pool 1)
    val (t2, r2) = in_thread (fn () => sum_in_pool 2)
    val _ = await_exits "caller threads did not exit" (fn () => [t1, t2])
    val _ = expect "two pools run side by side"
      (case (!r1, !r2) of
           (SOME (Exn.Res a), SOME (Exn.Res b)) =>
             a = [10, 11, 12, 13, 14, 15] andalso
             b = [20, 21, 22, 23, 24, 25]
         | _ => false)
  in
    ()
  end

val _ = test_hhPool ()

fun test_schedule_pool () =
  let
    open StagedFixture
    val pool_ranking = map (fn fact => "listTheory." ^ fact)
      ["MAP_APPEND", "LENGTH_MAP", "MAP_MAP_o", "APPEND_ASSOC",
       "APPEND_NIL", "LENGTH_APPEND", "REVERSE_APPEND"]
    val pool_goal : Term.term list * Term.term =
      ([], ``MAP (\y. y + 1n) (l ++ m) = MAP SUC (l ++ m)``)
    fun mono prover filter nfacts : hhProver.slice =
      {prover = prover, format = "tf0", type_enc = "mono_native",
       lam_trans = "combs", nfacts = nfacts, filter = filter,
       extra_opts = [], slice_size = 1}
    val schedule =
      [(e, mono Eprover "knn" 3), (e, legacy Eprover "knn" 2),
       (vampire, mono Vampire "knn" 5), (e, mono Eprover "knn" 7),
       (vampire, legacy Vampire "knn" 4), (e, mono Eprover "knn" 4)]
    val generated_count = 4
    (* Four consecutive generated jobs (no legacy item between them). *)
    val consecutive =
      [(e, mono Eprover "knn" 3), (vampire, mono Vampire "knn" 5),
       (e, mono Eprover "knn" 7), (vampire, mono Vampire "knn" 4)]
    val silent : hhSchedule.export_observer =
      {generated = fn _ => (), copied = fn _ => ()}
    fun no_temporaries root =
      List.all (not o String.isSuffix ".tmp") (root_files root)
    val plain = {fork = hhPool.default_fork, before_finish = fn _ => ()}
    (* The test hooks are global (hhSchedule_Test) and read once when an
       export starts; they are set for one export and restored after it.
       Concurrent exports must therefore start under the hooks they want
       and restore in the reverse order (see the concurrent test). *)
    fun using {fork, before_finish} observer root options goal rankings
        schedule =
      Portable.bracket
        (fn () => (!hhSchedule_Test.fork, !hhSchedule_Test.before_finish))
        (fn (old_fork, old_before) =>
           (hhSchedule_Test.fork := old_fork;
            hhSchedule_Test.before_finish := old_before))
        (fn _ =>
           (hhSchedule_Test.fork := fork;
            hhSchedule_Test.before_finish := before_finish;
            hhSchedule.export_problems_observed observer root options goal
              rankings schedule))
    (* A fixture: the goal, premise rankings and schedule of an export,
       and the explicit mono_instances cap, if any. *)
    type fixture =
      {label : string, goal : Abbrev.goal,
       rankings : (string * string list) list,
       schedule : (hhProver.prover_config * hhProver.slice) list,
       cap : int option}
    val pool_fixture : fixture =
      {label = "pool", goal = pool_goal,
       rankings = [("knn", pool_ranking)], schedule = schedule, cap = NONE}
    (* The TASK_13 fixture (v2): a goal with rigid type variables that
       clash with the premises', ground MAP uses at several types so that
       a small mono_instances cap binds, and a lambda that is not
       eta-reducible; the premises include o_DEF and S_DEF, so that helper
       lambda translation draws names.  Mono, poly and ?? encodings and the
       lifting modes. *)
    val v2_fixture : fixture =
      let
        fun arrow x y = Type.--> (x, y)
        val a = Type.alpha
        val b = Type.beta
        val num = Type.mk_type ("num", [])
        fun lst t = Type.mk_type ("list", [t])
        fun at tm ty = Term.inst (Type.match_type (Term.type_of tm) ty) tm
        fun map_at from to = at listSyntax.map_tm
          (arrow (arrow from to) (arrow (lst from) (lst to)))
        fun map_eq from to =
          let
            val f = Term.mk_var ("h", arrow from to)
            val l = Term.mk_var ("n", lst from)
            val tm = Term.list_mk_comb (map_at from to, [f, l])
          in boolSyntax.mk_eq (tm, tm) end
        val l = Term.mk_var ("l", lst a)
        val m = Term.mk_var ("m", lst a)
        val f = Term.mk_var ("f", arrow a b)
        val g = Term.mk_var ("g", arrow b a)
        val lb = Term.mk_var ("lb", lst b)
        val y = Term.mk_var ("y", b)
        val map_f = Term.list_mk_comb (map_at a b, [f, listSyntax.mk_append
          (l, m)])
        val goal0 = boolSyntax.mk_eq (map_f, listSyntax.mk_append
          (Term.list_mk_comb (map_at a b, [f, l]),
           Term.list_mk_comb (map_at a b, [f, m])))
        val lambda = Term.mk_abs (y, Term.mk_comb (g,
          Term.mk_comb (f, Term.mk_comb (g, y))))
        val goal5 = boolSyntax.mk_eq
          (Term.list_mk_comb (map_at b a, [lambda, lb]),
           Term.list_mk_comb (map_at b a, [g, Term.list_mk_comb
             (map_at a b, [f, Term.list_mk_comb (map_at b a, [g, lb])])]))
        val goal = boolSyntax.list_mk_conj
          (map (fn (from, to) => map_eq from to)
             [(num, Type.bool), (Type.bool, num), (num, num), (a, num),
              (num, a)] @ [goal0, goal5])
        fun gen format type_enc lam_trans nfacts : hhProver.slice =
          {prover = Eprover, format = format, type_enc = type_enc,
           lam_trans = lam_trans, nfacts = nfacts, filter = "knn",
           extra_opts = [], slice_size = 1}
        val ranking = map (fn (theory, fact) => theory ^ "Theory." ^ fact)
          [("list", "MAP_APPEND"), ("list", "LENGTH_MAP"),
           ("list", "MAP_MAP_o"), ("list", "APPEND_ASSOC"),
           ("combin", "o_THM"), ("combin", "K_THM"), ("combin", "I_THM"),
           ("combin", "S_THM"), ("list", "FOLDL"), ("combin", "o_DEF"),
           ("combin", "S_DEF")]
      in
        {label = "pool v2", goal = ([], goal),
         rankings = [("knn", ranking)],
         schedule =
           [(e, gen "tf0" "mono_native" "combs" 11),
            (e, legacy Eprover "knn" 4),
            (e, gen "tf1" "poly_native" "combs" 11),
            (vampire, gen "th1" "poly_native" "combs_and_lifting" 11),
            (vampire, legacy Vampire "knn" 6),
            (e, gen "fof" "mono_guards??" "combs" 11)],
         cap = SOME 3}
      end
    (* One export at a given counter start: its files (relative paths with
       their bytes) and the number of names drawn, counted by one read of
       the counter after the run. *)
    fun export_of (fx : fixture) hooks workers start =
      let
        val root = hhSchedule.new_problem_dir (hhConfig.state_dir ())
        val _ = advance_to start
        val first = counter ()
        val _ = quiet (fn () => using hooks silent
          root (options_capped 8 workers NONE NONE (#cap fx)) (#goal fx)
          (#rankings fx) (#schedule fx))
        val used = counter () - first - 1
        val files = tree root
      in
        (remove_tree root; (files, used, first))
      end
    val export = export_of pool_fixture
    (* The counter only moves forward, so the runs of one start follow one
       another: each begins where the previous one ended, used + 2 draws
       later (the draws of the export and one for each of the two readings
       of the counter).  The serial draw count, measured by a probe, places
       a start so that run j (0 is the serial one) draws names on both
       sides of a power of ten: it draws first+1 to first+used and the
       power lies in between.  Powers are crossed once, so the runs that
       follow are past it and must still give the serial bytes. *)
    fun straddles boundary (first, used) =
      first + 1 < boundary andalso boundary <= first + used
    (* Forced completion orders: the finishing work of index i waits for
       its gate; a controller thread opens the gates in the given order
       and waits for each job to finish before opening the next.  The
       indices of the generated jobs are 0, 2, 3 and 5.  The window is the
       number of workers and counts every item, the legacy ones too, so an
       order must let the head of the queue finish before a later job is
       admitted: with four workers job 0 is done before job 5 starts, and
       with two workers job 0 before job 3 and job 2 before job 5. *)
    val jobs = [0, 2, 3, 5]
    fun forced fx order workers start =
      let
        val m = new_monitor ()
        val opened = ref ([] : int list)
        val arrived = ref ([] : int list)
        val done_ = ref ([] : int list)
        fun member list i = List.exists (fn j => j = i) list
        fun gate i =
          (monitor_do m (fn () => arrived := i :: !arrived);
           monitor_until m "gate never opened" (fn () => member (!opened) i);
           monitor_do m (fn () => done_ := i :: !done_))
        val controller = Thread.fork (fn () =>
          List.app (fn i =>
            (monitor_until m "job never arrived"
               (fn () => member (!arrived) i);
             monitor_do m (fn () => opened := i :: !opened);
             monitor_until m "job never finished"
               (fn () => member (!done_) i))) order, [])
        val result = export_of fx
          {fork = hhPool.default_fork, before_finish = gate} workers start
        val _ = monitor_until m "controller did not finish"
          (fn () => length (!done_) = length order)
      in
        (result, rev (!done_))
      end
    fun check_fixture (fx : fixture) decades =
      let
        val prefix = #label fx ^ ": "
        val (_, probe_used, _) = export_of fx plain 1 (quiet_start ())
        (* The runs of the first start (the serial one, the two natural
           ones and the six forced ones) stay below the power. *)
        val span = 12 * (probe_used + 2)
        val power = power_above (counter () + span + 2000)
        fun crossing_start power run =
          power - run * (probe_used + 2) - probe_used div 2
        val starts =
          [(power - span - 1000, NONE), (crossing_start power 0, SOME 0)] @
          (if decades then [(crossing_start (10 * power) 3, SOME 3)] else [])
        fun check_start (start, crossing) =
          let
            val label = Int.toString start
            val boundary = if start > power then 10 * power else power
            val crossed = ref ([] : bool list)
            fun note (result as (_, used, first)) =
              (crossed := straddles boundary (first, used) :: !crossed;
               result)
            val (serial_files, serial_used, _) =
              note (export_of fx plain 1 start)
            val _ = expect (prefix ^ "the baseline exports every file at \
                \start " ^ label)
              (length serial_files = length (#schedule fx) andalso
               serial_used > 0)
            fun same what (files, used, _) =
              expect (prefix ^ what ^ " gives the serial bytes and counter \
                \at start " ^ label)
                (files = serial_files andalso used = serial_used)
            val _ = same "natural completion, 2 workers"
              (note (export_of fx plain 2 start))
            val _ = same "natural completion, 4 workers"
              (note (export_of fx plain 4 start))
            fun ordered order workers =
              let val (result, seen) = forced fx order workers start in
                (expect (prefix ^ "the gates opened in order " ^
                   String.concatWith "," (map Int.toString order) ^
                   " at start " ^ label)
                   (seen = order);
                 same ("forced order " ^ String.concatWith ","
                   (map Int.toString order) ^ ", " ^ Int.toString workers ^
                   " workers") (note result))
              end
            val _ =
              (ordered [3, 2, 0, 5] 4;
               ordered [2, 3, 0, 5] 4;
               ordered [0, 5, 3, 2] 4;
               ordered [2, 0, 3, 5] 4;
               ordered [2, 0, 5, 3] 2;
               ordered [0, 2, 3, 5] 2)
            val runs = rev (!crossed)
          in
            case crossing of
                NONE => expect (prefix ^ "no run straddles a power of ten \
                    \at start " ^ label)
                  (not (List.exists (fn x => x) runs))
              | SOME run => expect (prefix ^ "run " ^ Int.toString run ^
                  " draws names on both sides of a power of ten at start " ^
                  label) (List.nth (runs, run))
          end
      in
        List.app check_start starts
      end
    val _ = check_fixture pool_fixture true
    val _ = check_fixture v2_fixture false
    (* Cap: workers never exceed the generated jobs; one worker is inline
       (no thread is started). *)
    val forks = ref 0
    val counting = {fork = fn f => (forks := !forks + 1;
                                    hhPool.default_fork f),
                    before_finish = fn _ => ()}
    val _ = export counting 1 (quiet_start ())
    val inline_forks = !forks
    val _ = export counting 16 (quiet_start ())
    val _ = expect "pool: one worker runs inline, a pool starts a thread per \
      \generated job and no more"
      (inline_forks = 0 andalso !forks = generated_count)
    (* Failures and interrupts. *)
    fun with_root f =
      let val root = hhSchedule.new_problem_dir (hhConfig.state_dir ()) in
        (f root before remove_tree root)
        handle exn => (remove_tree root; raise exn)
      end
    (* A tail failure, as the first-order lambda handling raises it, and
       the text it had before the move (written out, not computed by
       describe_failure). *)
    val survivor : Term.term = ``\x:num. x + 1``
    fun survivor_text label =
      "hhProblemGen: " ^ label ^ ": hhProblemGen: lambda survived \
      \first-order lambda handling: " ^ Parse.term_to_string survivor
    fun path_of root index =
      hhSchedule.problem_path root (#2 (List.nth (schedule, index)))
    fun present root index = OS.FileSys.access (path_of root index, [])
    fun raw_export_on sched hooks observer workers root rankings_list =
      using hooks observer root (options_with 8 workers NONE NONE) pool_goal
        rankings_list sched
    fun raw_export hooks = raw_export_on schedule hooks
    fun run_export hooks observer workers root rankings_list =
      quiet (fn () => raw_export hooks observer workers root rankings_list)
    (* A fork wrapper that signals, through a monitor, when the function of
       the n-th started thread has returned (the job's outcome is then
       recorded and its slot freed). *)
    fun signalling_fork () =
      let
        val m = new_monitor ()
        val returned = ref ([] : int list)
        val count = ref 0
        val (fork, threads) = recording_fork (fn start => fn f =>
          let val n = monitor_do m (fn () => !count before count := !count + 1)
          in
            start (fn () =>
              (f (); monitor_do m (fn () => returned := n :: !returned)))
          end)
        fun wait_for n =
          monitor_until m ("worker " ^ Int.toString n ^ " did not return")
            (fn () => List.exists (fn j => j = n) (!returned))
      in (fork, threads, wait_for) end
    (* An early worker error, then a later prepare error.  The worker of
       index 2 fails (the hook raises, which works for any user, unlike a
       read-only directory); index 3's premise list is missing, so prepare
       fails there, and only after the worker thread of index 2 has
       returned.  The earliest failing index (2) is raised, the prefix is
       published and nothing else. *)
    val later_filter : hhProver.slice =
      {prover = Eprover, format = "tf0", type_enc = "mono_native",
       lam_trans = "combs", nfacts = 7, filter = "mepo", extra_opts = [],
       slice_size = 1}
    val failing_schedule =
      List.take (schedule, 3) @ [(e, later_filter)] @ List.drop (schedule, 4)
    fun early_error label failure expected = with_root (fn root =>
      let
        val (fork, threads, wait_for) = signalling_fork ()
        val observer : hhSchedule.export_observer =
          {generated = fn slice =>
             if #filter slice = "mepo" then wait_for 1 else (),
           copied = fn _ => ()}
        fun fail_two index = if index = 2 then raise failure else ()
        val outcome =
          (quiet (fn () => using
             {fork = fork, before_finish = fail_two} observer root
             (options_with 8 4 NONE NONE) pool_goal
             [("knn", pool_ranking), ("mepo", bad_ranking)]
             failing_schedule); "ok")
          handle Fail text => text | Feedback.HOL_ERR _ => "prepare"
      in
        expect label
          (outcome = expected andalso all_exited threads andalso
           present root 0 andalso
           present root 1 andalso not (present root 2) andalso
           not (present root 3) andalso not (present root 5) andalso
           no_temporaries root)
      end)
    val _ = early_error
      "pool: an early worker error beats a later prepare error"
      (Fail "worker") "worker"
    (* The failure of a tail on a worker is raw and becomes its text where
       the item is awaited, on the caller; the earliest failing index
       still wins over a later prepare error. *)
    val _ = early_error
      "pool: an early tail failure beats a later prepare error, as text"
      (hhProblemGen.Lambda_survived (["fact lemma"], survivor))
      (survivor_text "fact lemma")
    (* A prepare error alone: the earlier work is published. *)
    val _ = with_root (fn root =>
      let
        val (fork, threads) = recording_fork (fn start => start)
        val outcome =
          (quiet (fn () => using
             {fork = fork, before_finish = fn _ => ()} silent root
             (options_with 8 4 NONE NONE) pool_goal
             [("knn", pool_ranking), ("mepo", bad_ranking)]
             failing_schedule); "ok")
          handle Feedback.HOL_ERR _ => "prepare"
      in
        expect "pool: a prepare error publishes the prefix and stops workers"
          (outcome = "prepare" andalso all_exited threads andalso
           present root 0 andalso
           present root 1 andalso present root 2 andalso
           not (present root 3) andalso not (present root 5) andalso
           no_temporaries root)
      end)
    (* Partial launch: the third thread cannot be started. *)
    val _ = with_root (fn root =>
      let
        val calls = ref 0
        fun failing start f =
          (calls := !calls + 1;
           if !calls = 3 then raise Fail "no thread" else start f)
        val (fork, threads) = recording_fork failing
        val outcome =
          (run_export {fork = fork, before_finish = fn _ => ()} silent 4 root
             [("knn", pool_ranking)]; "ok")
          handle Fail "no thread" => "no thread"
      in
        expect "pool: a partial launch raises and publishes the prefix"
          (outcome = "no thread" andalso all_exited threads andalso
           present root 0 andalso
           present root 1 andalso present root 2 andalso
           not (present root 3) andalso not (present root 4) andalso
           not (present root 5) andalso no_temporaries root andalso
           length (threads ()) = 2)
      end)
    (* Gates for the interrupt and the concurrency tests: every
       generated job waits for its gate. *)
    fun gated () =
      let
        val m = new_monitor ()
        val released = ref false
        val arrived = ref 0
        fun gate _ =
          (monitor_do m (fn () => arrived := !arrived + 1);
           monitor_until m "gate never opened" (fn () => !released))
        fun release () = monitor_do m (fn () => released := true)
        fun arrived_count n =
          monitor_until m "jobs did not arrive" (fn () => !arrived = n)
        fun all_arrived () = arrived_count generated_count
      in (gate, release, all_arrived, arrived_count, fn () => !arrived) end
    (* An interrupt while the workers are busy: the caller is interrupted,
       the workers are interrupted, stopped and their files removed, and no
       file appears later.  Four consecutive generated jobs on four
       workers: the fourth arrival at its gate implies that every prepare
       is done (the caller touches no global state any more) and that the
       caller is awaiting job 0 or about to. *)
    val _ = with_root (fn root =>
      let
        val (gate, release, _, arrived_count, _) = gated ()
        val (fork, threads) = recording_fork (fn start => start)
        val result = ref NONE
        val caller = Thread.fork (fn () =>
          result := SOME (Exn.capture (fn () =>
            quiet (fn () => raw_export_on consecutive
              {fork = fork, before_finish = gate} silent 4 root
              [("knn", pool_ranking)])) ()), [])
        val _ = arrived_count 4
        val _ = Thread.interrupt caller
        val _ = await_exits "caller did not exit" (fn () => [caller])
        val _ = release ()
      in
        expect "pool: an interrupt propagates, stops workers, leaves no file"
          ((case !result of SOME (Exn.Exn Interrupt) => true | _ => false)
           andalso length (threads ()) = 4 andalso
           all_exited threads andalso null (root_files root))
      end)
    (* Cancelling a pool with a waiting job starts no thread for it: two
       workers, three consecutive generated jobs submitted (two run at
       their gates, one waits), the caller is interrupted, and the items
       are abandoned newest first, so no finalizer hands a slot to the
       waiting item.  The interrupt is sent once the third job has been
       submitted (a hook on the submit side), after which the caller
       blocks awaiting the first and prepares no fourth. *)
    val _ = with_root (fn root =>
      let
        val (gate, release, _, arrived_count, arrived) = gated ()
        val (fork, threads) = recording_fork (fn start => start)
        val submitted = new_monitor ()
        val third_submitted = ref false
        val old_after = !hhSchedule_Test.after_submit
        val result = ref NONE
        val caller = Thread.fork (fn () =>
          result := SOME (Exn.capture (fn () =>
            quiet (fn () =>
              let
                val _ = hhSchedule_Test.after_submit := (fn index =>
                  if index = 2 then
                    monitor_do submitted (fn () => third_submitted := true)
                  else ())
                val outcome = Exn.capture (fn () =>
                  using {fork = fork, before_finish = gate}
                    silent root (options_with 8 2 NONE NONE) pool_goal
                    [("knn", pool_ranking)] consecutive) ()
              in
                (hhSchedule_Test.after_submit := old_after;
                 Exn.release outcome)
              end)) ()), [])
        val _ = arrived_count 2
        val _ = monitor_until submitted "the third job was not submitted"
          (fn () => !third_submitted)
        val _ = Thread.interrupt caller
        val _ = await_exits "caller did not exit" (fn () => [caller])
        val _ = release ()
      in
        expect "pool: cancelling starts no thread for a waiting job"
          ((case !result of SOME (Exn.Exn Interrupt) => true | _ => false)
           andalso length (threads ()) = 2 andalso arrived () = 2 andalso
           all_exited threads andalso null (root_files root))
      end)
    (* Two concurrent invocations: the second runs completely while the
       workers of the first are busy. *)
    val _ = with_root (fn first_root => with_root (fn second_root =>
      let
        val (gate, release, _, arrived_count, _) = gated ()
        val first = ref NONE
        val second_outcome = ref (Exn.Res ())
        (* Far from a power of ten, so that the interleaved draws of the
           two invocations cannot change the order of the names. *)
        val concurrent_start = quiet_start ()
        val _ = advance_to concurrent_start
        (* Both invocations run under one redirection of the output (the
           redirection is a process-global stack, so two threads must not
           push and pop their own), and the second starts after the first
           has read its hooks and finishes, restoring them, before the first
           is released and restores its own. *)
        val _ = quiet (fn () =>
          let
            val caller = Thread.fork (fn () =>
              first := SOME (Exn.capture (fn () =>
                raw_export_on consecutive
                  {fork = hhPool.default_fork, before_finish = gate}
                  silent 4 first_root [("knn", pool_ranking)]) ()), [])
            (* Four consecutive generated jobs on four workers: the fourth
               arrival implies that every prepare of the first invocation
               is done and its caller is awaiting the first job. *)
            val _ = arrived_count 4
            val _ = second_outcome := Exn.capture (fn () =>
              raw_export plain silent 3 second_root
                [("knn", pool_ranking)]) ()
            val _ = release ()
          in
            await_exits "caller did not exit" (fn () => [caller])
          end)
        fun complete root sched =
          List.all (fn (_, slice) => OS.FileSys.access
            (hhSchedule.problem_path root slice, [])) sched andalso
          no_temporaries root
        fun generated_text root sched indices =
          map (fn index => String.concat (read_lines (hhSchedule.problem_path
                 root (#2 (List.nth (sched, index)))))) indices
        val (serial_files, _, _) = export plain 1 concurrent_start
        val (first_serial, _, _) = export_of
          {label = "pool", goal = pool_goal,
           rankings = [("knn", pool_ranking)], schedule = consecutive,
           cap = NONE} plain 1 concurrent_start
      in
        expect "pool: two concurrent invocations both complete"
          ((case (!first, !second_outcome) of
                (SOME (Exn.Res ()), Exn.Res ()) => true
              | _ => false) andalso complete first_root consecutive andalso
           complete second_root schedule andalso
           List.all (String.isPrefix "% generated by hhProblemGen")
             (generated_text first_root consecutive [0, 1, 2, 3] @
              generated_text second_root schedule jobs));
        expect "pool: two concurrent invocations give the serial bytes"
          (tree first_root = first_serial andalso
           tree second_root = serial_files)
      end))
    (* A pinned caller exports inline: the tail reads the ambient
       signature, which a fresh thread would see unpinned.  The constant
       exists only in the pin, so a tail on a worker could not even build
       the problem.  No thread is started with two workers configured, the
       bytes equal those of the one-worker export under the same pin, and
       the pin is neither released nor installed by the export. *)
    val _ =
      let
        val num = Type.mk_type ("num", [])
        val outcome = Context.with_context (Context.snapshot ()) (fn () =>
          let
            val _ = Theory.new_constant ("hh_pinned_only", num)
            val constant = Term.mk_const ("hh_pinned_only", num)
            val fx : fixture =
              {label = "pinned", goal = ([], boolSyntax.mk_eq (constant,
                 numSyntax.mk_plus (constant, numSyntax.zero_tm))),
               rankings = #rankings pool_fixture, schedule = schedule,
               cap = NONE}
            val start = quiet_start ()
            val forks = ref 0
            val counting = {fork = fn f => (forks := !forks + 1;
                                            hhPool.default_fork f),
                            before_finish = fn _ => ()}
            val (inline_files, _, _) = export_of fx counting 1 start
            val (pinned_files, _, _) = export_of fx counting 2 start
          in
            (inline_files, pinned_files, !forks, Context.is_pinned ())
          end) ()
        val (inline_files, pinned_files, forks, still_pinned) = outcome
      in
        expect "pool: a pinned caller exports inline with the pinned view"
          (length inline_files = length schedule andalso
           pinned_files = inline_files andalso forks = 0 andalso
           still_pinned andalso not (Context.is_pinned ()))
      end
    (* No pin is installed by an unpinned export, on the caller or on a
       worker. *)
    val _ =
      let
        val m = new_monitor ()
        val pinned_seen = ref false
        fun look _ = monitor_do m (fn () =>
          if Context.is_pinned () then pinned_seen := true else ())
        val _ = export {fork = hhPool.default_fork, before_finish = look}
          4 (quiet_start ())
      in
        expect "pool: an unpinned export installs no pin"
          (not (!pinned_seen) andalso not (Context.is_pinned ()))
      end
    (* Draw-freedom positive control: a worker that draws a fresh name
       (one per job here) is detected by the serial-equivalence check, which
       compares the number of names drawn. *)
    val _ =
      let
        val start = quiet_start ()
        val (serial_files, serial_used, _) = export plain 1 start
        val draw = {fork = hhPool.default_fork,
                    before_finish = fn _ => ignore (Type.gen_tyvar ())}
        val (_, drawn_used, _) = export draw 2 start
      in
        expect "pool: a draw on a worker is detected by the counter check"
          (drawn_used = serial_used + generated_count)
      end
    (* Draw-freedom of the tail itself, in every mode (the before_finish
       control above sees only the pooled path): for each generated slice
       of the fixtures, forcing the tail draws no fresh name, so the
       second counter read is one past the first. *)
    val _ = List.app (fn (fx : fixture) =>
      List.app (fn (config, slice : hhProver.slice) =>
        case hhSlice.encoding_of slice of
            hhSlice.Legacy => ()
          | hhSlice.Generated {format, type_enc, lam_trans} =>
              let
                val (hyps, concl) = #goal fx
                val ranking = #2 (valOf (List.find (fn (name, _) =>
                  name = #filter slice) (#rankings fx)))
                val named = List.filter (null o Thm.hyp o #2)
                  (smlRedirect.hidef mlThmData.thml_of_namel
                     (aiLib.first_n (#nfacts slice) ranking))
                val options =
                  {format = format, type_enc = type_enc,
                   lam_trans = lam_trans, mono_iters = 3,
                   mono_instances = Option.getOpt (#cap fx, 11)}
                val tail = hhProblemGen.prepare_pb
                  (hhProblemGen.new_export_memo ()) options
                  (boolSyntax.list_mk_imp (hyps, concl), named)
                val c0 = counter ()
                val _ = hhProblemGen.force_tail tail
                val c1 = counter ()
              in
                expect ("pool: the tail draws no fresh name, " ^ #label fx ^
                        " " ^ #format slice ^ " " ^ #type_enc slice ^ " " ^
                        #lam_trans slice)
                  (c1 = c0 + 1)
              end) (#schedule fx)) [pool_fixture, v2_fixture]
    (* A tail failing at index 2 (the injected failure) while the later
       tails succeed: the exception is the text, the prefix is published,
       nothing else is, and only the prepares the window admits happened:
       the failing item is awaited once the queue holds workers + 1 items,
       so index 0 .. min (5, 2 + workers) were prepared. *)
    val _ = List.app (fn workers => with_root (fn root =>
      let
        val prepares = ref 0
        val observer : hhSchedule.export_observer =
          {generated = fn _ => prepares := !prepares + 1,
           copied = fn _ => ()}
        fun fail_two index =
          if index = 2 then
            raise hhProblemGen.Lambda_survived (["conjecture"], survivor)
          else ()
        val outcome =
          (quiet (fn () => using
             {fork = hhPool.default_fork, before_finish = fail_two}
             observer root (options_with 8 workers NONE NONE) pool_goal
             [("knn", pool_ranking)] schedule); "ok")
          handle Fail text => text
      in
        expect ("pool: a tail failure, " ^ Int.toString workers ^
                " workers, is the text, the prefix stays, the prepares \
                \are bounded")
          (outcome = survivor_text "conjecture" andalso
           present root 0 andalso present root 1 andalso
           not (present root 2) andalso not (present root 3) andalso
           not (present root 5) andalso no_temporaries root andalso
           !prepares = Int.min (6, 3 + workers))
      end)) [2, 4]
    (* Nothing is written to the output by a worker: the output of a
       pooled export under hidef is that of the inline one (the caller
       alone prints nothing either), whichever thread would print. *)
    val _ =
      let
        fun output_of workers =
          let
            val file = OS.FileSys.tmpName ()
            val root = hhSchedule.new_problem_dir (hhConfig.state_dir ())
            val _ = smlRedirect.hide_in_file file (fn () =>
              using plain silent root (options_with 8 workers NONE NONE)
                pool_goal [("knn", pool_ranking)] schedule) ()
            val text = String.concat (read_lines file)
          in
            (OS.FileSys.remove file; remove_tree root; text)
          end
        val inline_output = output_of 1
        val pooled_output = output_of 4
      in
        expect "pool: workers write nothing to the output"
          (inline_output = "" andalso pooled_output = "")
      end
    (* Root removal: with_problem_dir removes the root of a pooled export,
       after a failure too; a debug root is kept and clean. *)
    fun reserved_export workers debug parent rankings_list schedule =
      let
        val seen = ref ""
        val outcome = (hhSchedule.with_problem_dir parent
          (options_with 8 workers debug NONE) (fn root =>
            (seen := root;
             quiet (fn () => using plain silent
               root (options_with 8 workers debug NONE) pool_goal
               rankings_list schedule))); "ok")
          handle Feedback.HOL_ERR _ => "prepare"
      in (outcome, !seen) end
    val _ =
      let
        val parent = hhSchedule.new_problem_dir (hhConfig.state_dir ())
        val (ok, root) = reserved_export 3 NONE parent
          [("knn", pool_ranking)] schedule
        val (bad, bad_root) = reserved_export 3 NONE parent
          [("knn", pool_ranking), ("mepo", bad_ranking)] failing_schedule
        val debug = hhSchedule.new_problem_dir (hhConfig.state_dir ())
        val (kept, kept_root) = reserved_export 3 (SOME debug) parent
          [("knn", pool_ranking)] schedule
      in
        expect "pool: with_problem_dir removes pooled roots, debug roots stay"
          (ok = "ok" andalso root <> "" andalso not (is_dir root) andalso
           bad = "prepare" andalso bad_root <> "" andalso
           not (is_dir bad_root) andalso kept = "ok" andalso
           is_dir kept_root andalso
           String.isPrefix debug kept_root andalso
           length (root_files kept_root) = length schedule andalso
           no_temporaries kept_root andalso null (list_directory parent));
        remove_tree parent;
        remove_tree debug
      end
  in
    ()
  end

(* The hoisted named fetch (once per filter at its largest count, prefixes
   by name) gives the theorems of the lazy fetch of each selection, and a
   missing theorem raises when the hoisted fetch is made. *)
fun test_schedule_hoisted_fetch () =
  let
    open StagedFixture
    val root = hhSchedule.new_problem_dir (hhConfig.state_dir ())
    val options = options_with 1 1 NONE NONE
    val twice = ["listTheory.APPEND_NIL", "listTheory.APPEND_NIL",
                 "listTheory.APPEND_ASSOC", "listTheory.LENGTH_APPEND"]
    val rankings = [("knn", ranking), ("mepo", twice)]
    val schedule =
      [(e, legacy Eprover "knn" 2), (vampire, legacy Vampire "knn" 2),
       (e, generated Eprover "knn" 3), (e, legacy Eprover "mepo" 3),
       (vampire, generated Vampire "mepo" 2),
       (e, generated Eprover "mepo" 4)]
    val works = hhSchedule.ordered_work root options rankings schedule
    val keys = List.mapPartial
      (fn {kind = hhSchedule.CopyLegacy _, ...} => NONE
        | {key, ...} => SOME key) works
    fun same left right =
      length left = length right andalso
      ListPair.all (fn ((n1, th1), (n2, th2)) =>
        n1 = n2 andalso Term.aconv (Thm.concl th1) (Thm.concl th2))
        (left, right)
    val lazy = hhSchedule.lazy_named rankings
    val hoisted = hhSchedule.hoisted_named rankings works
    val _ = expect "hoisted fetch gives the theorems of each lazy selection"
      (length keys = 5 andalso
       List.all (fn key => same (lazy key) (hoisted key)) keys)
    val _ = expect "hoisted fetch keeps a repeated name once per position"
      (map #1 (hoisted ("mepo", 2)) =
         ["listTheory.APPEND_NIL", "listTheory.APPEND_NIL"] andalso
       length (hoisted ("mepo", 3)) = 3)
    val missing = [("knn", ranking @ ["listTheory.NO_SUCH_THEOREM"])]
    val short = [(e, legacy Eprover "knn" 2), (e, generated Eprover "knn" 4)]
    val missing_works = hhSchedule.ordered_work root options missing short
    val _ = expect "a missing theorem raises when the hoisted fetch is made"
      ((ignore (hhSchedule.hoisted_named missing missing_works); false)
       handle _ => true)
    val _ = expect "a missing theorem raises at first use of the lazy fetch"
      (length (hhSchedule.lazy_named missing ("knn", 2)) = 2 andalso
       ((ignore (hhSchedule.lazy_named missing ("knn", 4)); false)
        handle _ => true))
  in
    remove_tree root
  end

(* The pipelined run_in (selected by hhSchedule_Test.pipelined).  Fixture:
   two fixture provers and five slices (two legacy, three generated) over
   the premises of a goal that Metis proves from LENGTH_APPEND.  Every
   prover reads its whole problem file when it starts; the blocking export
   of the same schedule, at a fresh counter start, gives the expected
   bytes.  Each run is on its own thread, so that a hang fails the test. *)
fun test_schedule_pipelined parser =
  let
    val gave_up = ["0", "e-gave-up.out"]
    val proof = ["0", "schedule-length-append.out"]
    val goal : Abbrev.goal = ([], ``LENGTH (l ++ m) = LENGTH l + LENGTH m``)
    fun names bad = map (fn fact => "listTheory." ^ fact)
      ["LENGTH_APPEND", "APPEND_NIL", "APPEND_ASSOC", "MAP_APPEND",
       "LENGTH_MAP", "REVERSE_APPEND", bad, "LENGTH_REVERSE"]
    val rankings = [("knn", names "MAP_MAP_o")]
    fun slice prover format type_enc lam_trans count extra : hhProver.slice =
      {prover = prover, format = format, type_enc = type_enc,
       lam_trans = lam_trans, nfacts = count, filter = "knn",
       extra_opts = extra, slice_size = 1}
    fun legacy prover count extra = slice prover "fof" "" "" count extra
    fun mono extra prover count =
      slice prover "tf0" "mono_native" "combs" count extra
    (* recording is the extra options of the legacy slices, monos those of
       the others. *)
    fun with_provers_mono monos recording note f =
      with_fixtures
        [(Vampire, printer_config_formats ["fof", "tf0"] "hh-pipe-v"
                [legacy Vampire 2 recording, mono monos Vampire 3,
                 mono monos Vampire 5] note parser),
         (Eprover, printer_config_formats ["fof", "tf0"] "hh-pipe-e"
                [legacy Eprover 2 recording, mono monos Eprover 7] note
                parser)]
        f
    fun with_provers recording note f =
      with_provers_mono gave_up recording note f
    (* A prover that runs for 30 s unless killed. *)
    val sleeper = ["30", "e-gave-up.out"]
    fun options_cores cores slices timeout max_proofs debug
        : hhConfig.hh_options =
      {timeout = timeout, max_proofs = max_proofs,
       provers = [Eprover, Vampire], slices = slices, cores = cores,
       export_workers = 2, filter = "", max_facts = NONE, format = "",
       type_enc = "", lam_trans = "", mono_iters = 3, mono_instances = NONE,
       minimize = true, preplay_timeout = 1.0, minimize_timeout = 1.0,
       cache = false, cache_dir = "", cache_max_entries = 100,
       debug_dir = debug, preplay_drop_one = false, verbose = false}
    val options = options_cores 8
    val tree = StagedFixture.tree
    val quiet_start = StagedFixture.quiet_start
    fun new_root () = hhSchedule.new_problem_dir (hhConfig.state_dir ())
    fun relative root path = String.extract (path, size root + 1, NONE)
    fun exists_prefix prefix events =
      List.exists (String.isPrefix prefix) events
    (* The selector and the test hooks are set for one run. *)
    fun with_hooks {pipelined, before_finish, before_prepare} f =
      Portable.bracket
        (fn () => (!hhSchedule_Test.pipelined, !hhSchedule_Test.before_finish,
                   !hhSchedule_Test.before_prepare))
        (fn (a, b, c) =>
           (hhSchedule_Test.pipelined := a;
            hhSchedule_Test.before_finish := b;
            hhSchedule_Test.before_prepare := c))
        (fn _ =>
           (hhSchedule_Test.pipelined := pipelined;
            hhSchedule_Test.before_finish := before_finish;
            hhSchedule_Test.before_prepare := before_prepare;
            f ()))
    fun hooks pipelined = {pipelined = pipelined, before_finish = fn _ => (),
                           before_prepare = fn _ => ()}
    (* The relative paths and generated-ness of the work of a schedule. *)
    fun is_generated ({kind = hhSchedule.ExportGenerated _, ...} :
                        hhSchedule.work) = true
      | is_generated _ = false
    fun work_list opts =
      let
        val root = new_root ()
        val works = with_provers gave_up ignore (fn () =>
          hhSchedule.ordered_work root opts rankings
            (hhSlice.mk_schedule opts))
      in
        (remove_tree root;
         map (fn w => (#index w, relative root (#path w), is_generated w))
           works)
      end
    (* The files of the blocking export of the schedule from a counter
       start, and the number of names it drew. *)
    fun expected opts start =
      let
        val root = new_root ()
        val schedule = with_provers gave_up ignore (fn () =>
          hhSlice.mk_schedule opts)
        val _ = advance_to start
        val first = counter ()
        val _ = StagedFixture.quiet (fn () =>
          hhSchedule.export_problems root opts goal rankings schedule)
        val used = counter () - first - 1
        val files = tree root
      in
        (remove_tree root; (files, used))
      end
    (* The state of a run, shared with the thread that steers it. *)
    fun new_state () =
      {root = new_root (), m = new_monitor (), released = ref false,
       events = ref ([] : string list),
       entered = ref ([] : (string * string * bool) list),
       reached = ref false, caller = ref (NONE : Thread.thread option),
       seen = ref (NONE : Thread.thread option), monos = ref gave_up}
    fun attempt f = (SOME (f ()), NONE) handle exn => (NONE, SOME exn)
    (* Runs run_in on its own thread, bounded by a wait; the result and
       the failure, if any. *)
    fun run st recording opts rks hooks' wrap start =
      let
        val {root, m, released, events, entered, caller, seen, ...} = st
        fun note (request : hhProver.run_request) =
          let val path = #problem request in
            monitor_do m (fn () =>
              entered := (relative root path,
                          String.concat (read_lines path), !released) ::
                         !entered)
          end
        fun progress event =
          monitor_do m (fn () =>
            events := observe_schedule_event event :: !events)
        val {pipelined, before_finish, before_prepare} = hooks'
        val tag_prepare = fn i =>
          ((if Option.isSome (!seen) then ()
            else seen := SOME (Thread.self ()));
           before_prepare i)
        val outcome = ref NONE
        val done_ = new_monitor ()
        val _ = advance_to start
        val _ = Thread.fork (fn () =>
          (caller := SOME (Thread.self ());
           outcome := SOME (attempt (fn () =>
             wrap (fn () =>
               with_provers_mono (!(#monos st)) recording note (fn () =>
                 with_hooks {pipelined = pipelined,
                             before_finish = before_finish,
                             before_prepare = tag_prepare} (fn () =>
                   hhSchedule.run_in root
                     {options = opts, goal = goal, rankings = rks,
                      progress = SOME progress}))))) ;
           monitor_do done_ (fn () => ())), [])
        val _ = monitor_until done_ "run_in did not finish"
          (fn () => Option.isSome (!outcome))
      in
        valOf (!outcome)
      end
    val no_wrap = fn f => f ()
    fun same_thread (seen : Thread.thread option ref,
                     caller : Thread.thread option ref) =
      case (!seen, !caller) of
          (SOME a, SOME b) => Thread.equal (a, b)
        | _ => false
    fun tmp_clean_names files =
      List.all (fn (name, _) => not (String.isSuffix ".tmp" name)) files
    fun lookup files path =
      Option.map #2 (List.find (fn (name, _) => name = path) files)

    (* The export states of the last pipelined run, by relative path. *)
    fun export_states root =
      map (fn (path, state) => (relative root path, state))
        (!hhSchedule_Test.export_states)
    fun state_of root path = lookup (export_states root) path
    fun all_ready root =
      List.all (fn (_, state) => state = hhSchedule_Test.Ready)
        (export_states root)
    fun none_pending root =
      List.all (fn (_, state) => state <> hhSchedule_Test.Pending)
        (export_states root)

    (* Readiness: a generated job held before its publication keeps
       neither the earlier legacy slice nor the later files back. *)
    fun readiness () =
      let
        val opts = options 5 30 1 NONE
        val works = work_list opts
        val n = length works
        val (held, held_path, _) =
          valOf (List.find (fn (_, _, generated) => generated) works)
        val admitted = Int.min (n - 1, held + 2)
        val start = quiet_start ()
        val (want, _) = expected opts start
        val st = new_state ()
        val {m, released, entered, events, root, ...} = st
        val gate = fn i =>
          if i = held then
            monitor_until m "the held job was never released"
              (fn () => !released)
          else ()
        val _ = Thread.fork (fn () =>
          (monitor_until m "slices did not start while the job was held"
             (fn () => length (!entered) >= admitted);
           monitor_do m (fn () => released := true)), [])
        val (result, failure) =
          run st gave_up opts rankings
            {pipelined = true, before_finish = gate,
             before_prepare = fn _ => ()} no_wrap start
        val seen = rev (!entered)
        val early = List.filter (fn (_, _, late) => not late) seen
        val files = tree root
        val _ = remove_tree root
      in
        (expect "pipelined: the run completes with every slice"
           (not (Option.isSome failure) andalso
            #stopped (valOf result) = hhSchedule.Exhausted andalso
            length (#slices_run (valOf result)) = n andalso
            length seen = n andalso
            schedule_events_sane (rev (!events)));
         expect "pipelined: slices start while a job is held"
           (length early = admitted andalso
            List.exists (fn (path, _, _) =>
              path = #2 (hd works)) early andalso
            List.exists (fn (path, _, _) =>
              List.exists (fn (index, p, _) => index > held andalso p = path)
                works) early andalso
            List.exists (fn (path, _, late) => path = held_path andalso late)
              seen);
         expect "pipelined: each prover reads the whole blocking file"
           (List.all (fn (path, text, _) => lookup want path = SOME text)
              seen);
         expect "pipelined: the published files are the blocking files"
           (files = want andalso tmp_clean_names files);
         expect "pipelined: every problem ends Ready"
           (all_ready root))
      end

    (* R1: a replay starts only after the last prepare.  A replay draws
       fresh names, as does a prepare; the pool tails and the provers
       draw none.  So while the last prepare is held, after the proof is
       found, the only draws are the two reads of the counters here.  The
       expected tree is for the same counter start; the counter only moves
       forward, so the run resumes after that export, within the same digit
       length (checked), which fixes the bytes. *)
    fun replay_after_prepares () =
      let
        val opts = options 5 30 10 NONE
        val works = work_list opts
        val last = length works - 1
        val start = quiet_start ()
        val (want, _) = expected opts start
        val st = new_state ()
        val {m, released, reached, events, root, ...} = st
        val at_found = ref (0, 0)
        val at_release = ref (0, 0)
        val held_verified = ref true
        val hold = fn i =>
          if i = last then
            (monitor_do m (fn () => reached := true);
             monitor_until m "the last prepare was never released"
               (fn () => !released))
          else ()
        val _ = Thread.fork (fn () =>
          (monitor_until m "no proof was found"
             (fn () => exists_prefix "found|" (!events));
           monitor_until m "the last prepare was not reached"
             (fn () => !reached);
           at_found := (counter (), genvar_counter ());
           OS.Process.sleep (Time.fromMilliseconds 700);
           at_release := (counter (), genvar_counter ());
           monitor_do m (fn () =>
             (held_verified := exists_prefix "verified|" (!events);
              released := true))), [])
        val (result, failure) =
          run st proof opts rankings
            {pipelined = true, before_finish = fn _ => (),
             before_prepare = hold} no_wrap start
        val finish = counter ()
        val files = tree root
        val _ = remove_tree root
      in
        (expect "pipelined: no name is drawn while the last prepare is held"
           (#1 (!at_release) = #1 (!at_found) + 1 andalso
            #2 (!at_release) = #2 (!at_found) + 1);
         expect "pipelined: no replay verifies before the last prepare"
           (not (!held_verified) andalso not (Option.isSome failure) andalso
            length (#suggestions (valOf result)) = 1 andalso
            exists_prefix "verified|" (!events));
         expect "pipelined: files beside a real replay equal the blocking ones"
           (size (Int.toString finish) = size (Int.toString start) andalso
            files = want);
         expect "pipelined: every problem ends Ready" (all_ready root))
      end

    (* The flag is set on an export error with the last prepare not yet
       done (it fails after a proof was found): the replay waiting for it
       is released by the stop, not by the flag alone, so it verifies
       nothing, and the run raises the error and does not hang. *)
    fun replay_after_error () =
      let
        val opts = options 5 30 10 NONE
        val works = work_list opts
        val last = length works - 1
        val (_, last_path, _) = List.last works
        val st = new_state ()
        val {m, events, root, ...} = st
        val fail = fn i =>
          if i = last then
            (monitor_until m "no proof was found"
               (fn () => exists_prefix "found|" (!events));
             raise Fail "injected prepare failure")
          else ()
        val (_, failure) =
          run st proof opts rankings
            {pipelined = true, before_finish = fn _ => (),
             before_prepare = fail} no_wrap (quiet_start ())
        val states_ok = none_pending root andalso
          state_of root last_path = SOME hhSchedule_Test.Failed
        val _ = remove_tree root
      in
        (expect "pipelined: an export error ends the run with the error"
           (case failure of
                SOME exn => contains "injected prepare failure"
                              (General.exnMessage exn)
              | NONE => false);
         expect "pipelined: no replay verifies after the export error"
           (not (exists_prefix "verified|" (!events)));
         expect "pipelined: an unfinished problem ends Failed" states_ok)
      end

    (* The flag is set when the producer is cancelled at the soft
       deadline: the replay then runs and the later file is not made.  The
       hold is at index 1, reached right after the first file, and lasts
       past the deadline of 1 s (the check of the producer precedes the
       hold), so the producer stops at the next prepare; the replay then
       has the grace time left to verify. *)
    fun replay_after_cancel () =
      let
        val opts = options 5 1 1 NONE
        val works = work_list opts
        val st = new_state ()
        val {m, released, reached, root, ...} = st
        val hold = fn i =>
          if i = 1 then
            (monitor_do m (fn () => reached := true);
             monitor_until m "the held prepare was never released"
               (fn () => !released))
          else ()
        val _ = Thread.fork (fn () =>
          (monitor_until m "the hold was not reached" (fn () => !reached);
           OS.Process.sleep (Time.fromMilliseconds 1100);
           monitor_do m (fn () => released := true)), [])
        val (result, failure) =
          run st proof opts rankings
            {pipelined = true, before_finish = fn _ => (),
             before_prepare = hold} no_wrap (quiet_start ())
        val (_, last_path, _) = List.last works
        val made = OS.FileSys.access (join root last_path, [])
        val states_ok = none_pending root andalso
          state_of root last_path = SOME hhSchedule_Test.Cancelled andalso
          state_of root (#2 (hd works)) = SOME hhSchedule_Test.Ready
        val _ = remove_tree root
      in
        (expect "pipelined: cancellation at the deadline frees the replay"
           (not (Option.isSome failure) andalso not made andalso
            length (#suggestions (valOf result)) = 1);
         expect "pipelined: the unprepared problems end Cancelled"
           states_ok)
      end

    (* ---- Stop, cancellation and the error race (TASK_24). ---- *)

    (* The test hooks of the launch and of the slice workers, and a fork
       that records the threads of the export pool, for one run. *)
    fun with_test_hooks {launch, claim, fork} f =
      Portable.bracket
        (fn () => (!hhSchedule_Test.launch_point,
                   !hhSchedule_Test.before_claim, !hhSchedule_Test.fork))
        (fn (a, b, c) =>
           (hhSchedule_Test.launch_point := a;
            hhSchedule_Test.before_claim := b;
            hhSchedule_Test.fork := c))
        (fn _ =>
           (hhSchedule_Test.launch_point := launch;
            hhSchedule_Test.before_claim := claim;
            hhSchedule_Test.fork := fork;
            f ()))
    fun producer_gone seen =
      case !seen of
          NONE => true
        | SOME thread => not (Thread.isActive thread)
    fun has_event prefix events = exists_prefix prefix (!events)
    fun event_count prefix events =
      length (List.filter (String.isPrefix prefix) (!events))
    (* A wait that no interrupt can cut: a loop that allocates and never
       blocks models a long prepare without a cancellation point. *)
    fun spin_until flag =
      let
        val limit = Time.+ (Time.now (), Time.fromSeconds 30)
        fun loop () =
          if !flag then ()
          else if Time.>= (Time.now (), limit) then raise Fail "spin limit"
          else (ignore (List.tabulate (20, Int.toString)); loop ())
      in loop () end
    fun until_stopped stopped =
      let
        val limit = Time.+ (Time.now (), Time.fromSeconds 30)
        fun loop () =
          if stopped () then ()
          else if Time.>= (Time.now (), limit) then raise Fail "no stop"
          else (OS.Process.sleep (Time.fromMilliseconds 5); loop ())
      in loop () end
    fun hooked fork = with_test_hooks
      {launch = fn _ => (), claim = fn _ => (), fork = fork}

    (* A verified first proof with max_proofs = 1 while an export is in
       flight (the tail of the last generated problem is held) and work
       is queued (each worker is held at its second claim until the run
       stops): the queued work never starts, the held tail is cancelled
       and its file is not made, and every thread has exited when run_in
       returns. *)
    fun stop_after_proof () =
      let
        val opts = options_cores 2 5 30 1 NONE
        val works = work_list opts
        val (held, held_path, _) =
          List.last (List.filter (fn (_, _, generated) => generated) works)
        val st = new_state ()
        val {m, released, entered, root, ...} = st
        val _ = (#monos st) := sleeper
        val (fork, recorded) = recording_fork (fn default => default)
        val callers = ref ([] : Thread.thread list)
        val gate = fn i =>
          if i = held then
            monitor_until m "the held tail was never released"
              (fn () => !released)
          else ()
        val claim = fn stopped =>
          let
            val me = Thread.self ()
            val again = monitor_do m (fn () =>
              if List.exists (fn other => Thread.equal (other, me))
                   (!callers) then true
              else (callers := me :: !callers; false))
          in
            if again then until_stopped stopped else ()
          end
        val (result, failure) =
          run st proof opts rankings
            {pipelined = true, before_finish = gate,
             before_prepare = fn _ => ()}
            (with_test_hooks {launch = fn _ => (), claim = claim,
                              fork = fork})
            (quiet_start ())
        val files = tree root
        val started = length (!entered)
        val _ = remove_tree root
      in
        (expect "stop: a verified first proof stops the run (max_proofs 1)"
           (not (Option.isSome failure) andalso
            #stopped (valOf result) = hhSchedule.MaxProofs andalso
            length (#suggestions (valOf result)) = 1 andalso
            schedule_events_sane (rev (!(#events st))));
         expect "stop: queued work stays unstarted"
           (started >= 1 andalso started <= 2 andalso
            length (#slices_run (valOf result)) = started);
         expect "stop: the export in flight is cancelled"
           (not (!released) andalso lookup files held_path = NONE andalso
            state_of root held_path = SOME hhSchedule_Test.Cancelled andalso
            none_pending root andalso tmp_clean_names files);
         expect "stop: the producer and the pool threads have exited"
           (producer_gone (#seen st) andalso all_exited recorded andalso
            #t_total (valOf result) < 20.0))
      end

    (* Soft timeout with only pending work: every problem waits for the
       export, which is held in a wait; the deadline cancels it at once
       (before the hard deadline, 3 s here) and nothing runs. *)
    fun soft_timeout_pending () =
      let
        val opts = options 5 1 1 NONE
        val st = new_state ()
        val {m, released, reached, root, ...} = st
        val hold = fn i =>
          if i = 0 then
            (monitor_do m (fn () => reached := true);
             monitor_until m "the held prepare was never released"
               (fn () => !released))
          else ()
        val (fork, recorded) = recording_fork (fn default => default)
        val (result, failure) =
          run st gave_up opts rankings
            {pipelined = true, before_finish = fn _ => (),
             before_prepare = hold} (hooked fork) (quiet_start ())
        val files = tree root
        val states = export_states root
        val _ = remove_tree root
      in
        (expect "stop: the soft deadline cancels a producer that waits"
           (not (Option.isSome failure) andalso !reached andalso
            #stopped (valOf result) = hhSchedule.Timeout andalso
            #t_total (valOf result) < 2.5 andalso
            null (#slices_run (valOf result)) andalso null files);
         expect "stop: the cancelled problems end Cancelled"
           (not (null states) andalso
            List.all (fn (_, state) => state = hhSchedule_Test.Cancelled)
              states andalso
            has_event "schedule-done|timeout" (#events st) andalso
            producer_gone (#seen st) andalso all_exited recorded))
      end

    (* Hard timeout with running work: the provers ignore the soft
       deadline and are killed at the hard one; the producer, held at the
       last prepare, has been cancelled by then. *)
    fun hard_timeout_running () =
      let
        val opts = options 5 1 1 NONE
        val works = work_list opts
        val last = length works - 1
        val st = new_state ()
        val {m, released, root, ...} = st
        val hold = fn i =>
          if i = last then
            monitor_until m "the held prepare was never released"
              (fn () => !released)
          else ()
        val (result, failure) =
          run st sleeper opts rankings
            {pipelined = true, before_finish = fn _ => (),
             before_prepare = hold} no_wrap (quiet_start ())
        val files = tree root
        val _ = remove_tree root
      in
        (expect "stop: the hard deadline kills the running provers"
           (not (Option.isSome failure) andalso
            #stopped (valOf result) = hhSchedule.Timeout andalso
            #t_total (valOf result) > 2.5 andalso
            #t_total (valOf result) < 15.0 andalso
            has_event "schedule-done|timeout" (#events st) andalso
            event_count "started|" (#events st) >= 1);
         expect "stop: the held producer has exited and nothing is left"
           (producer_gone (#seen st) andalso tmp_clean_names files))
      end

    (* The first fatal export error wins over a run that is still
       searching: running provers are killed, the error is raised on the
       caller and no ScheduleDone is reported. *)
    fun error_wins () =
      let
        val opts = options 5 30 1 NONE
        val works = work_list opts
        val last = length works - 1
        val st = new_state ()
        val {m, entered, root, ...} = st
        val fail = fn i =>
          if i = last then
            (monitor_until m "no slice started"
               (fn () => length (!entered) >= 1);
             raise Fail "injected export error")
          else ()
        val (fork, recorded) = recording_fork (fn default => default)
        val begun = Time.now ()
        val (result, failure) =
          run st sleeper opts rankings
            {pipelined = true, before_finish = fn _ => (),
             before_prepare = fail} (hooked fork) (quiet_start ())
        val took = Time.toReal (Time.- (Time.now (), begun))
        val files = tree root
        val _ = remove_tree root
      in
        (expect "error: an export error is raised on the caller"
           (not (Option.isSome result) andalso
            (case failure of
                 SOME exn => contains "injected export error"
                               (General.exnMessage exn)
               | NONE => false));
         expect "error: no ScheduleDone and the provers are killed"
           (not (has_event "schedule-done|" (#events st)) andalso
            took < 20.0 andalso not (has_event "verified|" (#events st)));
         expect "error: everything has stopped"
           (producer_gone (#seen st) andalso all_exited recorded andalso
            tmp_clean_names files andalso none_pending root))
      end

    (* The other order: a caller interrupt arrives while the producer is
       in a prepare that cannot be cut (it spins), so the run is stopping
       when the prepare then fails.  The late error is dropped, the run
       ends Interrupted, and it does not return before the prepare ends:
       the response is bounded by one prepare, and no later prepare is
       started. *)
    fun stop_wins () =
      let
        val opts = options 5 30 1 NONE
        val held = 2
        val st = new_state ()
        val {m, released, reached, events, caller, entered, root, ...} = st
        val prepared = ref ([] : int list)
        val early_done = ref true
        val spin = fn i =>
          (monitor_do m (fn () => prepared := i :: !prepared);
           if i = held then
             (monitor_do m (fn () => reached := true);
              spin_until released;
              raise Fail "late export error")
           else ())
        val _ = Thread.fork (fn () =>
          (monitor_until m "the prepare was not reached" (fn () => !reached);
           monitor_until m "no slice started"
             (fn () => length (!entered) >= 1);
           Thread.interrupt (valOf (!caller));
           OS.Process.sleep (Time.fromMilliseconds 500);
           monitor_do m (fn () =>
             (early_done := exists_prefix "schedule-done|" (!events);
              released := true))), [])
        val (fork, recorded) = recording_fork (fn default => default)
        val (result, failure) =
          run st sleeper opts rankings
            {pipelined = true, before_finish = fn _ => (),
             before_prepare = spin} (hooked fork) (quiet_start ())
        val files = tree root
        val states = export_states root
        val works = work_list opts
        val later = List.filter (fn (i, _, _) => i > held) works
        val _ = remove_tree root
      in
        (expect "interrupt: the late export error of a stopped run is dropped"
           (not (Option.isSome failure) andalso
            #stopped (valOf result) = hhSchedule.Interrupted andalso
            has_event "schedule-done|interrupted" (#events st) andalso
            schedule_events_sane (rev (!events)));
         expect "interrupt: the run waits for the prepare in progress"
           (not (!early_done));
         expect "interrupt: no prepare starts after the stop"
           (List.all (fn i => i <= held) (!prepared) andalso
            List.all (fn (_, path, _) =>
              lookup states path = SOME hhSchedule_Test.Cancelled) later andalso
            none_pending root andalso tmp_clean_names files);
         expect "interrupt: the producer and the pool have exited"
           (producer_gone (#seen st) andalso all_exited recorded))
      end

    (* A caller interrupt during the export: the producer is interrupted
       where it waits (here: the hook), the provers are killed and the run
       ends Interrupted before it returns. *)
    fun interrupt_during_export () =
      let
        val opts = options 5 30 1 NONE
        val st = new_state ()
        val {m, released, reached, caller, entered, root, ...} = st
        val hold = fn i =>
          if i = 2 then
            (monitor_do m (fn () => reached := true);
             monitor_until m "the held prepare was never released"
               (fn () => !released))
          else ()
        val _ = Thread.fork (fn () =>
          (monitor_until m "the prepare was not reached" (fn () => !reached);
           monitor_until m "no slice started"
             (fn () => length (!entered) >= 1);
           Thread.interrupt (valOf (!caller))), [])
        val (fork, recorded) = recording_fork (fn default => default)
        val (result, failure) =
          run st sleeper opts rankings
            {pipelined = true, before_finish = fn _ => (),
             before_prepare = hold} (hooked fork) (quiet_start ())
        val _ = remove_tree root
      in
        (expect "interrupt: an interrupt of the caller stops the producer"
           (not (Option.isSome failure) andalso
            #stopped (valOf result) = hhSchedule.Interrupted andalso
            #t_total (valOf result) < 15.0 andalso
            schedule_events_sane (rev (!(#events st))));
         expect "interrupt: the producer and the pool have exited"
           (producer_gone (#seen st) andalso all_exited recorded))
      end

    (* An interrupt of the caller at each launch point (a raise of
       Interrupt by the hook, as an asynchronous one would be): the run
       ends Interrupted, with ScheduleDone, and every thread it forked has
       exited, also the producer that was forked and the ones that were
       not.  The producer is held at its first prepare. *)
    fun interrupt_during_launch () =
      let
        val points = ["recon-registered", "recon-forked",
                      "producer-registered", "producer-forked",
                      "worker-registered", "worker-forked"]
        fun scenario point =
          let
            val opts = options 5 30 1 NONE
            val st = new_state ()
            val {m, released, root, ...} = st
            val fired = ref false
            val launch = fn name =>
              if name = point andalso not (!fired) then
                (fired := true; raise Interrupt)
              else ()
            val hold = fn i =>
              if i = 0 then
                monitor_until m "the held prepare was never released"
                  (fn () => !released)
              else ()
            val (fork, recorded) = recording_fork (fn default => default)
            val (result, failure) =
              run st gave_up opts rankings
                {pipelined = true, before_finish = fn _ => (),
                 before_prepare = hold}
                (with_test_hooks {launch = launch, claim = fn _ => (),
                                  fork = fork})
                (quiet_start ())
            val states = export_states root
            val _ = remove_tree root
          in
            expect ("interrupt at launch point " ^ point ^
                    ": Interrupted, then ScheduleDone, all exited")
              (not (Option.isSome failure) andalso !fired andalso
               #stopped (valOf result) = hhSchedule.Interrupted andalso
               has_event "schedule-done|interrupted" (#events st) andalso
               schedule_events_sane (rev (!(#events st))) andalso
               producer_gone (#seen st) andalso all_exited recorded andalso
               List.all (fn (_, state) => state <> hhSchedule_Test.Pending)
                 states)
          end
      in
        List.app scenario points
      end

    (* Overlapping invocations with different goals, each its own root:
       both verify their own goal. *)
    fun overlapping () =
      let
        val goal_b : Abbrev.goal =
          ([], ``LENGTH (l ++ m ++ n) = LENGTH l + LENGTH m + LENGTH n``)
        val opts = options 5 30 1 NONE
        val finished = new_monitor ()
        fun invocation goal =
          let
            val root = new_root ()
            val out = ref NONE
            val _ = Thread.fork (fn () =>
              (out := SOME (attempt (fn () =>
                 hhSchedule.run_in root
                   {options = opts, goal = goal, rankings = rankings,
                    progress = SOME (fn _ => ())}));
               monitor_do finished (fn () => ())), [])
          in
            (root, out)
          end
        fun proves (goal : Abbrev.goal) (result : hhSchedule.result) =
          case #suggestions result of
              [suggestion] =>
                (ignore (Tactical.TAC_PROOF (goal, #tac suggestion)); true)
                handle Interrupt => raise Interrupt | _ => false
            | _ => false
        val ((root_a, out_a), (root_b, out_b)) =
          with_provers proof ignore (fn () =>
            with_hooks (hooks true) (fn () =>
              let
                val a = invocation goal
                val b = invocation goal_b
                val _ = monitor_until finished "overlapping runs did not end"
                  (fn () => Option.isSome (!(#2 a)) andalso
                            Option.isSome (!(#2 b)))
              in (a, b) end))
        val tree_a = tree root_a
        val tree_b = tree root_b
        val _ = (remove_tree root_a; remove_tree root_b)
        fun ok goal out =
          case valOf (!out) of
              (SOME result, NONE) =>
                #stopped result = hhSchedule.MaxProofs andalso
                proves goal result
            | _ => false
      in
        (expect "overlap: each invocation verifies its own goal"
           (ok goal out_a andalso ok goal_b out_b);
         expect "overlap: each root holds its own complete files"
           (tmp_clean_names tree_a andalso tmp_clean_names tree_b andalso
            not (null tree_a) andalso not (null tree_b)))
      end

    (* Where the export runs. *)
    fun selection () =
      let
        fun scenario opts rks pipelined wrap =
          let
            val st = new_state ()
            val (result, failure) =
              run st gave_up opts rks (hooks pipelined) wrap
                (quiet_start ())
            val files = tree (#root st)
            val _ = remove_tree (#root st)
          in
            (st, result, failure, files)
          end
        val normal = options 5 30 1 NONE
        val debug = OS.FileSys.tmpName ()
        val _ = remove_tree debug
        val (blocking, _, _, _) = scenario normal rankings false no_wrap
        val (piped, piped_result, _, _) =
          scenario normal rankings true no_wrap
        val (debugged, _, _, _) =
          scenario (options 5 30 1 (SOME debug)) rankings true no_wrap
        val (pinned, _, _, _) = scenario normal rankings true
          (fn f => Context.with_context (Context.snapshot ()) f ())
        val (empty, empty_result, _, _) =
          scenario (options 0 30 1 NONE) rankings true no_wrap
        val missing = [("knn", names "NO_SUCH_THEOREM")]
        val (absent, _, absent_failure, absent_files) =
          scenario normal missing true no_wrap
        val _ = remove_tree debug
      in
        (expect "pipelined: the export is on the caller by default"
           (same_thread (#seen blocking, #caller blocking));
         expect "pipelined: the selected export runs on its own thread"
           (Option.isSome (!(#seen piped)) andalso
            not (same_thread (#seen piped, #caller piped)) andalso
            #stopped (valOf piped_result) = hhSchedule.Exhausted);
         expect "pipelined: debug_dir keeps the blocking export"
           (same_thread (#seen debugged, #caller debugged));
         expect "pipelined: a pinned caller keeps the blocking export"
           (same_thread (#seen pinned, #caller pinned));
         expect "pipelined: an empty schedule behaves as before"
           (#stopped (valOf empty_result) = hhSchedule.Exhausted andalso
            null (#slices_run (valOf empty_result)) andalso
            not (Option.isSome (!(#seen empty))));
         expect "pipelined: a missing theorem raises before any file"
           (Option.isSome absent_failure andalso null absent_files andalso
            null (!(#events absent)) andalso
            not (Option.isSome (!(#seen absent)))))
      end
  in
    (List.app (fn _ => readiness ()) [1, 2, 3, 4, 5];
     replay_after_prepares ();
     replay_after_error ();
     replay_after_cancel ();
     stop_after_proof ();
     soft_timeout_pending ();
     hard_timeout_running ();
     error_wins ();
     stop_wins ();
     interrupt_during_export ();
     interrupt_during_launch ();
     overlapping ();
     selection ())
  end

val _ = test_schedule_pool ()
val _ = test_schedule_pipelined (#parse_output (prover Eprover))
val _ = test_schedule_hoisted_fetch ()
val _ = test_schedule_knn_anchor_export ()
val _ = test_schedule_mono_cap_export ()
val _ = test_hhSchedule ()

(* The scheduler tests run once more on the pipelined path (the selector
   is restored afterwards, whatever happens). *)
fun with_pipelined f =
  Portable.bracket (fn () => !hhSchedule_Test.pipelined)
    (fn old => hhSchedule_Test.pipelined := old)
    (fn _ => (hhSchedule_Test.pipelined := true; f ()))

val _ = with_pipelined test_hhSchedule

fun test_main_hh_lemmas_hook parser =
  let
    val hook : string -> mlThmData.thmdata -> Abbrev.goal ->
      string list option =
      holyHammer.main_hh_lemmas
    val name = "hh-main-lemmas-hook"
    val launches = ref 0
    val slices =
      [fixture_slice Z3 ["0", "schedule-truth.out"] 1,
       fixture_slice Z3 ["5", "schedule-t-def.out"] 1,
       fixture_slice Z3 ["0", "schedule-add1.out"] 1]
    fun note _ = launches := !launches + 1
    val settings =
      [("provers", hhConfig.prover_name Z3), ("slices", "3"),
       ("cores", "1"), ("timeout", "5"), ("filter", "none"),
       ("debug_dir", "")]
    val lemmas =
      with_fixtures [(Z3, printer_config name slices note parser)] (fn () =>
        with_hh_options settings (fn () =>
          hook (hhConfig.state_dir ()) mlThmData.empty_thmdata
            ([], boolSyntax.T)))
    val _ = expect "main_hh_lemmas returns scheduler suggestion lemmas"
      (lemmas = SOME ["boolTheory.TRUTH"])
    val _ = expect "interactive HolyHammer stops after one verified proof"
      (!launches < length slices)
  in
    ()
  end

fun test_holyHammer_unverified_failure parser =
  let
    val name = "hh-main-unverified"
    val slice = fixture_slice Z3
      ["0", "schedule-unreconstructable.out"] 1
    val debug = OS.FileSys.tmpName ()
    val _ = remove_tree debug
    val problem = ref ""
    val config = printer_config name [slice]
      (fn request => problem := #problem request) parser
    val settings =
      [("provers", hhConfig.prover_name Z3), ("slices", "1"),
       ("cores", "1"), ("timeout", "5"), ("filter", "none"),
       ("debug_dir", debug)]
    val goal = ([], Thm.concl (DB.fetch "arithmetic" "ADD1"))
    val message =
      with_fixtures [(Z3, config)] (fn () =>
        with_hh_options settings (fn () =>
          hh_error (fn () => ignore
            (holyHammer.main_hh debug mlThmData.empty_thmdata goal))))
    val _ = expect "unverified ATP proofs are reported with diagnostics"
      (case message of
           SOME text =>
             contains name text andalso
             contains "fixtureTheory.unreconstructable" text andalso
             contains (!problem) text andalso
             String.isPrefix (debug ^ "/") (!problem) andalso
             OS.FileSys.access (!problem, []) andalso
             contains debug text andalso
             contains "output:" text
         | NONE => false)
    val _ = remove_tree debug
  in
    ()
  end

fun test_holyHammer_scheduler_api () =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      SOME _ => ()
    | NONE =>
        let val parser = #parse_output (prover Eprover) in
          test_main_hh_lemmas_hook parser;
          test_holyHammer_unverified_failure parser
        end

val _ = test_holyHammer_scheduler_api ()
val _ = with_pipelined test_holyHammer_scheduler_api

fun test_hhEval_integration () =
  case OS.Process.getEnv "HHCONFIG_TEST_ROOT" of
      SOME _ => ()
    | NONE =>
  case OS.Process.getEnv "HHEVAL_INTEGRATION_TEST" of
      SOME _ =>
        let
          val root =
            case OS.Process.getEnv "HOL4_HAMMER_EVAL_DIR" of
                SOME path => path
              | NONE => raise Fail "integration test has no evaluation dir"
          val condition : hhEval.condition =
            {cond_id = "bushy-deps-e", regime = hhEval.Bushy,
             selector = hhEval.Deps, engine = hhEval.Prover Eprover,
             timeout = 1,
             reconstruct = false}
          val scheduled : hhEval.condition =
            {cond_id = "runtime-options", regime = hhEval.Bushy,
             selector = hhEval.Deps,
             engine = hhEval.Sched {provers = [Eprover], slices = 1,
               cores = 1, max_proofs = 1, export_workers = 1},
             timeout = 1, reconstruct = true}
          fun run expname conditions = with_hh_options
            [("filter", "mepo"), ("format", "tf0"),
             ("type_enc", "mono_native"), ("lam_trans", "lifting")]
            (fn () => hhEval.run_eval
              {expname = expname, ncore = 1, thyl = ["pair", "option"],
               conditions = conditions})
          val _ = run "smoke" [condition]
          val expdir = join root "smoke"
          val pair_journal = hhEval.journal_path expdir "pair"
          val option_journal = hhEval.journal_path expdir "option"
          val journal_before = String.concat (read_lines pair_journal) ^
            String.concat (read_lines option_journal)
          val _ = expect "hhEval integration journals are valid"
            (not (null (hhEval.read_journal pair_journal)) andalso
             not (null (hhEval.read_journal option_journal)) andalso
             OS.FileSys.access (join expdir "run.json", [OS.FileSys.A_READ]))
          fun script_exists thy =
            OS.FileSys.access (hhEval.evalscript_path expdir thy, [])
          val _ = expect "hhEval removes worker scripts after the run"
            (not (script_exists "pair") andalso not (script_exists "option"))
          (* Simulates a driver killed before its cleanup handlers ran. *)
          val _ = write_file (hhEval.evalscript_path expdir "pair") "\n"
          val _ = run "smoke" [condition]
          val _ = expect "hhEval resume sweeps stale worker scripts"
            (not (script_exists "pair"))
          val journal_after = String.concat (read_lines pair_journal) ^
            String.concat (read_lines option_journal)
          val _ = expect "hhEval integration resume is a no-op"
            (journal_before = journal_after)
          val changed : hhEval.condition =
            {cond_id = #cond_id condition, regime = #regime condition,
             selector = #selector condition, engine = #engine condition,
             timeout = 2, reconstruct = #reconstruct condition}
          val rejected =
            ((run "smoke" [changed]; false)
             handle Fail message =>
               String.isSubstring "conditions differs" message)
          val _ = expect "hhEval rejects incompatible completed runs"
            (rejected andalso journal_before =
              String.concat (read_lines pair_journal) ^
              String.concat (read_lines option_journal))
          val _ = run "worker-options" [scheduled]
          val worker_dir = join root "worker-options"
          val worker_slices = List.concat (map #slices
            (hhEval.read_journal (hhEval.journal_path worker_dir "pair") @
             hhEval.read_journal (hhEval.journal_path worker_dir "option")))
          val _ = expect "hhEval workers use runtime schedule settings"
            (not (null worker_slices) andalso
             List.all (fn {slice, ...} : hhEval.journal_slice =>
               #filter slice = "mepo" andalso #format slice = "tf0" andalso
               #type_enc slice = "mono_native" andalso
               #lam_trans slice = "lifting") worker_slices)
        in
          ()
        end
    | NONE =>
        (case hhProver.probe (prover Eprover) of
             NONE => (tprint "hhEval integration (skipped: e absent)"; OK ())
           | SOME _ =>
               (tprint
                  "hhEval integration (skipped: set HHEVAL_INTEGRATION_TEST)";
                OK ()))

val _ = test_hhEval_integration ()

val _ = expect
  "hhEval smoke retains twelve legacy prover goals and one schedule goal"
  (length hhEval.smoke_goals = 16 andalso
   length (List.filter (fn (_, _, kind) => kind = hhEval.SmokeSched)
     hhEval.smoke_goals) = 1)

val _ = expect "hhEval smoke covers every pinned prover four times"
  (List.all (fn prover =>
     length (List.filter (fn (_, _, kind) => kind = hhEval.SmokeProver prover)
       hhEval.smoke_goals) = 4)
   [hhProver.Eprover, hhProver.Vampire, hhProver.Zipperposition])

val _ = expect "hhEval smoke adds one goal for every ensemble filter"
  (List.all (fn kind =>
     length (List.filter (fn (_, _, item) => item = kind)
       hhEval.smoke_goals) = 1)
   [hhEval.SmokeMepo, hhEval.SmokeMash, hhEval.SmokeMesh])

fun test_hhEval_pool_restriction () =
  let
    val pool = ["kept", "other", "kept"]
    val features =
      [("absent", [0]), ("kept", [1]), ("other", [2]), ("tail", [3])]
    fun old_restrict rows = List.filter (fn (name, _) =>
      List.exists (fn allowed => allowed = name) pool) rows
  in
    expect "hhEval set pool restriction preserves old rows and order"
      (hhEval.restrict_features_to_pool pool features = old_restrict features)
  end

val _ = test_hhEval_pool_restriction ()

fun test_hhStature_pure () =
  let
    val truth = DB.fetch "bool" "TRUTH"
    val deltas =
      [ThmSetData.ADD ({Thy = "first", Name = "kept"}, truth),
       ThmSetData.ADD ({Thy = "first", Name = "removed"}, truth),
       ThmSetData.ADD ({Thy = "second", Name = "removed"}, truth),
       ThmSetData.REMOVE "removed",
       ThmSetData.ADD ({Thy = "second", Name = "other"}, truth),
       ThmSetData.REMOVE "second.other"]
    val simp_names = hhStature.simp_thmids_of_deltas deltas
    val list_induction = TypeBase.induction_of ``:'a list``
    val conclusions = hhStature.induction_concls_of [list_induction]
    val p = Term.mk_var
      ("P", Type.mk_type ("fun", [Type.bool, Type.bool]))
    val x = Term.mk_var ("x", Type.bool)
    val quantified_predicate = boolSyntax.mk_forall
      (p, boolSyntax.mk_imp (Term.mk_comb (p, boolSyntax.T),
                            Term.mk_comb (p, x)))
    val ordinary = boolSyntax.mk_forall (x, boolSyntax.mk_eq (x, x))
  in
    expect "hhStature folds simp ADD and REMOVE deltas"
      (simp_names = ["firstTheory.kept"]);
    expect "hhStature recognizes a TypeBase induction conclusion"
      (hhStature.induction_by_concl conclusions
        (Thm.concl list_induction));
    expect "hhStature rejects an induct-named ordinary fact"
      (not (hhStature.induction_by_shape
        "fixtureTheory.not_really_induct" ordinary));
    expect "hhStature requires an induct name for predicate shape"
      (not (hhStature.induction_by_shape
        "fixtureTheory.quantified_predicate" quantified_predicate));
    expect "hhStature accepts induct name plus predicate shape"
      (hhStature.induction_by_shape
        "fixtureTheory.custom_INDUCT" quantified_predicate)
  end

val _ = test_hhStature_pure ()

fun test_hhStature_registered_definition () =
  let
    val inherited_simp = "arithmeticTheory.NOT_LT_ZERO_EQ_ZERO"
    val raw_name = "hh_stature_fixture_raw_def"
    val registered_name = "hh_stature_registered_fixture"
    val constant = Term.mk_var ("hh_stature_fixture", Type.bool)
    val raw_definition = boolSyntax.new_definition
      (raw_name, boolSyntax.mk_eq (constant, boolSyntax.T))
    val _ = Theory.save_thm (registered_name, raw_definition)
    val _ = BasicProvers.export_rewrites [raw_name]
    val _ = DefnBaseCore.register_defn
      {tag = "user", thmname = registered_name}
    val inherited_statures = hhStature.create_statures ()
    val inherited = hhStature.stature_of inherited_statures inherited_simp
    val _ = BasicProvers.delsimps
      ["arithmetic.NOT_LT_ZERO_EQ_ZERO"]
    val statures = hhStature.create_statures ()
    val removed = hhStature.stature_of statures inherited_simp
    val raw = hhStature.stature_of statures
      ("hhStatureTestTheory." ^ raw_name)
    val registered = hhStature.stature_of statures
      ("hhStatureTestTheory." ^ registered_name)
    val explicit_target = hhStature.stature_of
      (hhStature.create_statures_for "arithmetic")
      "arithmeticTheory.ADD1"
    val explicit_inherited = hhStature.stature_of
      (hhStature.create_statures_for "arithmetic") inherited_simp
    val explicit_unrelated = hhStature.stature_of
      (hhStature.create_statures_for "arithmetic")
      ("hhStatureTestTheory." ^ raw_name)
    val explicit_unrelated_induction = hhStature.stature_of
      (hhStature.create_statures_for "arithmetic")
      "hhStatureTestTheory.hh_typeenc_recursive_induction"
    val explicit_ancestor_induction = hhStature.stature_of
      (hhStature.create_statures_for "list") "boolTheory.bool_INDUCT"
    val explicit_target_induction = hhStature.stature_of
      (hhStature.create_statures_for "list") "listTheory.list_induction"
    val explicit_ancestor_definition = hhStature.stature_of
      (hhStature.create_statures_for "list") "boolTheory.LET_DEF"
    val namespace = hhStature.stature_of statures
      (mlThmData.namespace_tag ^ "Theory." ^ registered_name)
  in
    expect "hhStature includes an inherited simp theorem"
      (#simp inherited);
    expect "hhStature honors a local removal of an inherited simp theorem"
      (not (#simp removed));
    expect "hhStature detects a DB-class definition" (#def raw);
    expect "hhStature detects a DefnBase-registered theorem"
      (#def registered andalso #local_ registered);
    expect "hhStature accepts an explicit logical target theory"
      (#local_ explicit_target);
    expect "hhStature target retains its ancestor simp deltas"
      (#simp explicit_inherited);
    expect "hhStature target ignores unrelated ambient simp deltas"
      (not (#simp explicit_unrelated) andalso
       not (#local_ explicit_unrelated) andalso
       not (#def explicit_unrelated) andalso
       not (#induction explicit_unrelated));
    expect "hhStature target ignores unrelated ambient TypeBase rows"
      (not (#simp explicit_unrelated_induction) andalso
       not (#local_ explicit_unrelated_induction) andalso
       not (#def explicit_unrelated_induction) andalso
       not (#induction explicit_unrelated_induction));
    expect "hhStature target includes ancestor TypeBase induction rows"
      (#induction explicit_ancestor_induction andalso
       not (#local_ explicit_ancestor_induction));
    expect "hhStature target includes target TypeBase induction rows"
      (#induction explicit_target_induction andalso
       #local_ explicit_target_induction);
    expect "hhStature target includes ancestor definition and DB rows"
      (#def explicit_ancestor_definition andalso
       not (#local_ explicit_ancestor_definition));
    expect "hhStature gives namespace theorems no stature"
      (not (#simp namespace) andalso not (#local_ namespace) andalso
       not (#def namespace) andalso not (#induction namespace))
  end

val _ = test_hhStature_registered_definition ()

fun mepo_has_pconst name ptype pconsts =
  List.exists (fn (name', ptype') =>
    name = name' andalso hhMePo.ptype_eq (ptype, ptype')) pconsts

fun mepo_has_name name pconsts =
  List.exists (fn (name', _) => name = name') pconsts

fun test_hhMePo_matching_and_defaults () =
  let
    val alpha = Term.type_of ``x : 'a``
    val beta = Term.type_of ``x : 'b``
    val bool_list = Term.type_of ``[T]``
    val alpha_list = Term.type_of ``[] : 'a list``
    val bool_type = Type.bool
    val num_type = Term.type_of ``0``
    val fudge = hhMePo.default_fudge
    fun real_eq left right = Real.compare (left, right) = EQUAL
  in
    expect "hhMePo keeps all Isabelle defaults in its fudge record"
      (real_eq (#local_const_multiplier fudge) 1.5 andalso
       real_eq (#worse_irrel_freq fudge) 100.0 andalso
       real_eq (#higher_order_irrel_weight fudge) 1.05 andalso
       real_eq (#abs_rel_weight fudge) 0.5 andalso
       real_eq (#abs_irrel_weight fudge) 2.0 andalso
       real_eq (#theory_const_rel_weight fudge) 0.5 andalso
       real_eq (#theory_const_irrel_weight fudge) 0.25 andalso
       real_eq (#chained_const_irrel_weight fudge) 0.25 andalso
       real_eq (#intro_bonus fudge) 0.15 andalso
       real_eq (#elim_bonus fudge) 0.15 andalso
       real_eq (#simp_bonus fudge) 0.15 andalso
       real_eq (#local_bonus fudge) 0.55 andalso
       real_eq (#assum_bonus fudge) 1.05 andalso
       real_eq (#chained_bonus fudge) 1.5 andalso
       real_eq (#max_imperfect fudge) 11.5 andalso
       real_eq (#max_imperfect_exp fudge) 1.0 andalso
       real_eq (#threshold_divisor fudge) 2.0 andalso
       real_eq (#ridiculous_threshold fudge) 0.1 andalso
       real_eq (#fact_threshold0 fudge) 0.45 andalso
       real_eq (#fact_threshold1 fudge) 0.85 andalso
       real_eq (#perfect_threshold fudge) 0.99999 andalso
       real_eq (#hopeless_threshold fudge) 0.001 andalso
       #special_fact_index fudge = 45 andalso #hopeless_iter fudge = 5);
    expect "hhMePo type variables match arbitrary instances"
      (hhMePo.match_patternT (alpha, bool_type) andalso
       hhMePo.match_patternT (beta, bool_list));
    expect "hhMePo concrete type matching is structural"
      (hhMePo.match_patternT (alpha_list, bool_list) andalso
       not (hhMePo.match_patternT (bool_list, alpha_list)) andalso
       not (hhMePo.match_patternT (bool_type, num_type)));
    expect "hhMePo match_ptype ignores order in the I direction"
      (hhMePo.match_ptype ((0, [alpha]), (7, [bool_type])));
    expect "hhMePo match_ptype distinguishes the swap direction"
      (not (hhMePo.match_ptype ((7, [bool_type]), (0, [alpha]))));
    expect "hhMePo match_ptype accepts a shorter instance list only"
      (hhMePo.match_ptype ((0, [alpha, bool_type]),
                           (0, [bool_type])) andalso
       not (hhMePo.match_ptype ((0, [bool_type]),
                                (0, [alpha, bool_type]))))
  end

val _ = test_hhMePo_matching_and_defaults ()

fun test_hhMePo_extraction () =
  let
    val bool_type = Type.bool
    val instantiated = hhMePo.pconsts_in_term "fixture"
      ``CONS T [] = [T]``
    val skeleton = hhMePo.pconsts_in_term "fixture"
      ``!x : bool. ?y : bool. ?!z : bool.
          (p x /\ q y) \/ ~r z ==>
          (s x = if c then t y else u z)``
    val restricted =
      let
        val function_type = Type.mk_type ("fun", [Type.bool, Type.bool])
        val x = Term.mk_var ("x", Type.bool)
        val restriction = Term.mk_var ("restriction", function_type)
        val body = Term.mk_comb (Term.mk_var ("body", function_type), x)
      in
        hhMePo.pconsts_in_term "fixture"
          (boolSyntax.mk_res_forall (x, restriction, body))
      end
    val restricted_exists =
      let
        val function_type = Type.mk_type ("fun", [Type.bool, Type.bool])
        val x = Term.mk_var ("x", Type.bool)
        val restriction = Term.mk_var ("exists_restriction", function_type)
        val body = Term.mk_comb
          (Term.mk_var ("exists_body", function_type), x)
      in
        hhMePo.pconsts_in_term "fixture"
          (boolSyntax.mk_res_exists (x, restriction, body))
      end
    val set_term = hhMePo.pconsts_in_term "fixture"
      ``x IN {y | p y}``
    val bare_abs = hhMePo.pconsts_in_term "fixture"
      ``\x : bool. p x``
    val equality_rhs = hhMePo.pconsts_in_term "fixture"
      ``(f : bool -> bool) = (\x. p x)``
    val applied_abs = hhMePo.pconsts_in_term "fixture"
      ``h (\x : bool. p x)``
    val skeleton_names = ["p", "q", "r", "s", "c", "t", "u"]
    val skeleton_consts =
      ["min$=", "min$==>", "bool$T", "bool$F", "bool$~",
       "bool$/\\", "bool$\\/", "bool$COND", "bool$LET", "bool$!",
       "bool$?", "bool$?!"]
  in
    expect "hhMePo extracts polymorphic constant type arguments"
      (mepo_has_pconst "list$CONS" (1, [bool_type]) instantiated andalso
       mepo_has_pconst "list$NIL" (0, [bool_type]) instantiated);
    expect "hhMePo adds one collision-free theory pseudo-constant"
      (mepo_has_pconst "%thy%fixture" (0, []) instantiated);
    expect "hhMePo strips the complete formula skeleton"
      (List.all (fn name => mepo_has_name name skeleton) skeleton_names andalso
       List.all (fn name => not (mepo_has_name name skeleton))
         skeleton_consts);
    expect "hhMePo traverses restricted quantifier predicates and bodies"
      (mepo_has_name "restriction" restricted andalso
       mepo_has_name "body" restricted andalso
       not (mepo_has_name "bool$RES_FORALL" restricted) andalso
       mepo_has_name "exists_restriction" restricted_exists andalso
       mepo_has_name "exists_body" restricted_exists andalso
       not (mepo_has_name "bool$RES_EXISTS" restricted_exists));
    expect "hhMePo skips set constants but traverses their arguments"
      (mepo_has_name "x" set_term andalso mepo_has_name "p" set_term andalso
       not (mepo_has_name "bool$IN" set_term) andalso
       not (mepo_has_name "pred_set$GSPEC" set_term));
    expect "hhMePo records unapplied abstractions"
      (mepo_has_pconst "%abs" (1, []) bare_abs andalso
       mepo_has_pconst "%abs" (1, []) applied_abs andalso
       not (mepo_has_name "x" bare_abs));
    expect "hhMePo suppresses an equality RHS abstraction"
      (not (mepo_has_name "%abs" equality_rhs))
  end

val _ = test_hhMePo_extraction ()

fun test_hhMePo_frequency () =
  let
    val bool_type = Type.bool
    val alpha = Term.type_of ``x : 'a``
    val table = hhMePo.count_fact_consts
      [("A", ``(f : bool -> bool) x /\ f x``),
       ("B", ``(f : bool -> bool) x = x``)]
    val typed_table = hhMePo.count_fact_consts
      [("C", ``MEM T [T]``), ("D", ``MEM 0 [0]``)]
    val abstraction_table = hhMePo.count_fact_consts
      [("E", ``\bound : bool. predicate bound``)]
    fun exact table pconst =
      hhMePo.pconst_freq (fn (left, right) =>
        hhMePo.ptype_eq (left, right)) table pconst
  in
    expect "hhMePo raw frequency counts repeated function occurrences"
      (exact table ("f", (1, [])) = 3);
    expect "hhMePo raw frequency counts repeated arguments"
      (exact table ("x", (0, [])) = 4);
    expect "hhMePo raw frequency retains conjunction"
      (exact table ("bool$/\\", (1, [])) = 1);
    expect "hhMePo raw frequency retains polymorphic equality"
      (exact table ("min$=", (1, [bool_type])) = 1);
    expect "hhMePo raw frequency counts each fact's theory once"
      (exact table ("%thy%A", (0, [])) = 1 andalso
       exact table ("%thy%B", (0, [])) = 1);
    expect "hhMePo frequency matching sums polymorphic instances"
      (hhMePo.pconst_freq hhMePo.match_ptype typed_table
         ("list$CONS", (0, [alpha])) = 2);
    expect "hhMePo frequency matching keeps concrete instances distinct"
      (hhMePo.pconst_freq hhMePo.match_ptype typed_table
         ("list$CONS", (0, [bool_type])) = 1);
    expect "hhMePo absent frequencies are total and zero"
      (exact table ("missing", (0, [])) = 0);
    expect "hhMePo raw frequencies ignore binders and abs pseudo-constants"
      (exact abstraction_table ("predicate", (1, [])) = 1 andalso
       exact abstraction_table ("bound", (0, [])) = 0 andalso
       exact abstraction_table ("%abs", (1, [])) = 0)
  end

val _ = test_hhMePo_frequency ()

fun mepo_real_close expected actual =
  Real.abs (expected - actual) < 0.000000001

val mepo_plain_stature : hhStature.stature =
  {simp = false, local_ = false, def = false, induction = false}

val mepo_local_stature : hhStature.stature =
  {simp = false, local_ = true, def = false, induction = false}

fun test_hhMePo_weight_arithmetic () =
  let
    val fudge = hhMePo.default_fudge
    val function_type = Type.mk_type ("fun", [Type.bool, Type.bool])
    val f = Term.mk_var ("f", function_type)
    val x = Term.mk_var ("x", Type.bool)
    val frequency = hhMePo.count_fact_consts
      [("Fixture", Term.mk_comb (f, x))]
    val f_pconst = ("f", (1, []))
    val x_pconst = ("x", (0, []))
    val rel_table = hhMePo.add_pconst_to_table f_pconst
      (hhMePo.empty_pconst_table ())
    val chained_table = hhMePo.add_pconst_to_table x_pconst
      (hhMePo.empty_pconst_table ())
    val rel = 1.5 * (1.0 + 2.0 / Math.ln 2.0)
    val irrel =
      1.5 * (Math.ln 2.0 / Math.ln 100.0) / 1.05 * 0.25
    val score = hhMePo.fact_weight fudge mepo_plain_stature frequency
      rel_table chained_table [f_pconst, x_pconst]
    val simp_local : hhStature.stature =
      {simp = true, local_ = true, def = false, induction = false}
    val candidates =
      ("perfect-a", 1.1) :: ("perfect-b", 1.0) ::
      List.tabulate (20, fn index =>
        ("imperfect-" ^ Int.toString index,
         0.9 - Real.fromInt index / 100.0))
    val (accepted, left) = hhMePo.take_most_relevant fudge
      {max_facts = 20, remaining_max = 20, candidates = candidates}
    val before_purge = [("low", 0.0009), ("boundary", 0.001)]
  in
    expect "hhMePo relevant rarity weight is verbatim"
      (mepo_real_close (1.0 + 2.0 / Math.ln 2.0)
        (hhMePo.rel_weight_for 7 1));
    expect "hhMePo irrelevant frequency and order curve is verbatim"
      (mepo_real_close (Math.ln 2.0 / Math.ln 100.0 / 1.05)
        (hhMePo.irrel_weight_for fudge 0 1));
    expect "hhMePo applies free and chained multipliers in fact_weight"
      (mepo_real_close (rel / (rel + irrel)) score);
    expect "hhMePo uses fixed abstraction and theory weights"
      (mepo_real_close 0.5
         (hhMePo.rel_pconst_weight fudge frequency ("%abs", (3, [])))
       andalso
       mepo_real_close 0.25
         (hhMePo.irrel_pconst_weight fudge frequency chained_table
           ("%thy%Fixture", (0, []))));
    expect "hhMePo simp status shadows the local stature bonus"
      (mepo_real_close 0.15
        (hhMePo.stature_bonus fudge simp_local) andalso
       mepo_real_close 0.55
        (hhMePo.stature_bonus fudge mepo_local_stature));
    expect "hhMePo accepts all perfect and at most twelve imperfect facts"
      (length accepted = 14 andalso length left = 8 andalso
       map #1 (List.take (accepted, 2)) = ["perfect-a", "perfect-b"]);
    expect "hhMePo purges only sub-0.001 hopeless facts at iteration five"
      (map #1 (hhMePo.purge_hopeless fudge 4 before_purge) =
         ["low", "boundary"] andalso
       case hhMePo.purge_hopeless fudge 5 before_purge of
           [(name, weight)] =>
             name = "boundary" andalso mepo_real_close 0.001 weight
         | _ => false)
  end

val _ = test_hhMePo_weight_arithmetic ()

fun mepo_context current facts =
  hhMePo.make_context {current_theory = current, facts = facts}

fun mepo_fixture thmid theory concl stature =
  {thmid = thmid, theory = theory, concl = concl, stature = stature}

fun test_hhMePo_loop_thresholds_and_goal_context () =
  let
    val p = Term.mk_var ("mepo_p", Type.bool)
    val q = Term.mk_var ("mepo_q", Type.bool)
    val noise = List.tabulate (50, fn index =>
      Term.mk_var ("mepo_noise_" ^ Int.toString index, Type.bool))
    val threshold_fact = boolSyntax.list_mk_conj (p :: noise)
    val threshold_context = mepo_context "Fixture"
      [mepo_fixture "FixtureTheory.threshold_halved" "Fixture"
        threshold_fact mepo_plain_stature]
    val fallback_context = mepo_context "Fixture"
      [mepo_fixture "FixtureTheory.local_fallback" "Fixture" p
         mepo_local_stature,
       mepo_fixture "OtherTheory.not_local" "Other" q
         mepo_plain_stature]
    val assumption_context = mepo_context "Fixture"
      [mepo_fixture "FixtureTheory.from_asl" "Fixture" q
         mepo_plain_stature]
    val dirty_context = mepo_context "Fixture"
      [mepo_fixture "FixtureTheory.first_round" "Fixture"
         (boolSyntax.mk_conj (p, q)) mepo_plain_stature,
       mepo_fixture "OtherTheory.dirty_rescore" "Other" q
         mepo_plain_stature]
    val duplicate_context = mepo_context "Fixture"
      [mepo_fixture "FixtureTheory.duplicate" "Fixture"
         (boolSyntax.mk_conj (p, q)) mepo_plain_stature,
       mepo_fixture "FixtureTheory.duplicate" "Fixture"
         (boolSyntax.mk_conj (p,
           Term.mk_var ("mepo_duplicate_other", Type.bool)))
         mepo_plain_stature,
       mepo_fixture "OtherTheory.after_duplicate" "Other" q
         mepo_plain_stature]
    val chain_symbols = List.tabulate (7, fn index =>
      Term.mk_var ("mepo_chain_" ^ Int.toString index, Type.bool))
    val chain_facts = List.tabulate (6, fn index =>
      mepo_fixture ("ChainTheory.step_" ^ Int.toString index)
        ("Chain" ^ Int.toString index)
        (boolSyntax.mk_conj (List.nth (chain_symbols, index),
          List.nth (chain_symbols, index + 1))) mepo_plain_stature)
    val purge_context = mepo_context "Fixture"
      (chain_facts @
       [mepo_fixture "HopelessTheory.never_relevant" "Hopeless"
          (Term.mk_var ("mepo_hopeless", Type.bool))
          mepo_plain_stature])
    val restricted = hhMePo.restrict_context fallback_context
      ["OtherTheory.not_local"]
  in
    expect "hhMePo retries an empty first iteration at half threshold"
      (hhMePo.mepo_rank threshold_context ([], p) 1 =
       ["FixtureTheory.threshold_halved"]);
    expect "hhMePo falls back from a constant-free goal to local facts"
      (hhMePo.mepo_rank fallback_context ([], boolSyntax.T) 1 =
       ["FixtureTheory.local_fallback"]);
    expect "hhMePo adds assumptions to the goal and chained tables"
      (hhMePo.mepo_rank assumption_context ([q], boolSyntax.T) 1 =
       ["FixtureTheory.from_asl"]);
    expect "hhMePo invalidates cached weights for newly relevant constants"
      (hhMePo.mepo_rank dirty_context ([], p) 2 =
       ["FixtureTheory.first_round", "OtherTheory.dirty_rescore"]);
    expect "hhMePo keeps duplicate-thmid candidate payloads distinct"
      (hhMePo.mepo_rank duplicate_context ([], p) 3 =
       ["FixtureTheory.duplicate", "FixtureTheory.duplicate",
        "OtherTheory.after_duplicate"]);
    expect "hhMePo full loop reaches iteration-five hopeless purging"
      (hhMePo.mepo_rank purge_context
         ([], hd chain_symbols) 6 = map #thmid chain_facts);
    expect "hhMePo context restriction preserves requested pool order"
      (hhMePo.context_thmids restricted = ["OtherTheory.not_local"])
  end

val _ = test_hhMePo_loop_thresholds_and_goal_context ()

fun test_hhMePo_special_facts () =
  let
    val p = Term.mk_var ("mepo_special_p", Type.bool)
    val arity_zero =
      ``(CONS : bool -> bool list -> bool list) = CONS``
    val arity_one = ``CONS T = CONS T``
    val goal =
      ``mepo_special_p /\
        ((CONS : bool -> bool list -> bool list) = CONS) /\
        mepo_special_x IN (mepo_special_s : bool set)``
    val regular =
      mepo_fixture "FixtureTheory.arity_zero" "Fixture" arity_zero
        mepo_plain_stature ::
      mepo_fixture "FixtureTheory.arity_one" "Fixture" arity_one
        mepo_plain_stature ::
      List.tabulate (48, fn index =>
        mepo_fixture ("FixtureTheory.regular_" ^ Int.toString index)
          "Fixture" p mepo_plain_stature)
    val specials =
      [mepo_fixture "boolTheory.EQ_EXT" "bool" p mepo_plain_stature,
       mepo_fixture "pred_setTheory.SPECIFICATION" "pred_set" p
         mepo_plain_stature,
       mepo_fixture "pred_setTheory.GSPECIFICATION" "pred_set" p
         mepo_plain_stature,
       mepo_fixture "boolTheory.IN_DEF" "bool" p mepo_plain_stature]
    val context = mepo_context "Fixture" (regular @ specials)
    val ranking = hhMePo.mepo_rank context ([], goal) 54
  in
    expect "hhMePo inserts set and arity-extensionality facts at index 45"
      (length ranking = 54 andalso
       List.take (List.drop (ranking, 45), 4) =
         ["boolTheory.EQ_EXT", "pred_setTheory.SPECIFICATION",
          "pred_setTheory.GSPECIFICATION", "boolTheory.IN_DEF"])
  end

val _ = test_hhMePo_special_facts ()

fun test_hhMePo_live_context_constructor () =
  let
    val thmid = "arithmeticTheory.ADD1"
    val theorem = DB.fetch "arithmetic" "ADD1"
    val thmdata : mlThmData.thmdata =
      (#1 mlThmData.empty_thmdata, [(thmid, [])])
    val context = hhMePo.create_context thmdata
      (hhStature.create_statures ())
  in
    expect "hhMePo live context fetches and ranks named theorem conclusions"
      (hhMePo.context_thmids context = [thmid] andalso
       hhMePo.mepo_rank context ([], Thm.concl theorem) 1 = [thmid])
  end

val _ = test_hhMePo_live_context_constructor ()

fun learn_real_close expected actual =
  Real.abs (expected - actual) < 0.000000001

fun test_hhLearn_constants_idf_and_dependencies () =
  let
    val constants = hhLearn.default_constants
    val facts =
      [("FixtureTheory.a", [1, 1, 2]),
       ("FixtureTheory.b", [2, 3]),
       ("FixtureTheory.c", [2])]
    val idf = hhLearn.create_idf_table facts
    val calls = ref ([] : string list)
    fun dependencies thmid =
      (calls := thmid :: !calls;
       if thmid = "FixtureTheory.a" then ["FixtureTheory.base"] else [])
    val dep_table = hhLearn.build_dep_table dependencies
      (facts @ [("FixtureTheory.a", [9])])
  in
    expect "hhLearn centralizes the verbatim sparse-NB constants"
      (learn_real_close 30.0 (#init_val constants) andalso
       learn_real_close 5.0 (#pos_weight constants) andalso
       learn_real_close ~18.0 (#def_val constants) andalso
       learn_real_close 0.2 (#tau constants) andalso
       #def_prior_weight constants = 1000 andalso
       #max_dependencies constants = 20);
    expect "hhLearn computes plain IDF in one fact-list fold"
      (hhLearn.idf_nfacts idf = 3 andalso
       hhLearn.document_frequency idf 1 = SOME 1 andalso
       hhLearn.document_frequency idf 2 = SOME 3 andalso
       hhLearn.document_frequency idf 3 = SOME 1 andalso
       case (hhLearn.idf_of idf 1, hhLearn.idf_of idf 2,
             hhLearn.idf_of idf 3) of
           (SOME one, SOME two, SOME three) =>
             learn_real_close (Math.ln 3.0) one andalso
             learn_real_close 0.0 two andalso
             learn_real_close (Math.ln 3.0) three
         | _ => false);
    expect "hhLearn builds each dependency-table entry once"
      (length (!calls) = 3 andalso
       hhLearn.dependencies_of dep_table "FixtureTheory.a" =
         SOME ["FixtureTheory.base"] andalso
       hhLearn.dependencies_of dep_table "FixtureTheory.missing" = NONE)
  end

val _ = test_hhLearn_constants_idf_and_dependencies ()

fun learn_fact thmid features def concl : hhLearn.fact_info =
  {thmid = thmid, features = features, def = def, concl = concl}

fun learn_model facts dependencies =
  let
    val feature_facts = map (fn (fact : hhLearn.fact_info) =>
      (#thmid fact, #features fact)) facts
  in
    hhLearn.train_nb hhLearn.default_constants
      (hhLearn.create_idf_table feature_facts)
      (hhLearn.dep_table_of dependencies) facts
  end

fun test_hhLearn_nb_counts_and_scores () =
  let
    val facts =
      [learn_fact "A" [1, 2] false NONE,
       learn_fact "B" [2, 3] false NONE,
       learn_fact "C" [4] false NONE]
    val model = learn_model facts
      [("A", []), ("B", ["A"]), ("C", [])]
    val goal_features = [(1, 1.0), (4, 0.5), (999, 1000000.0)]
    val parts = valOf (hhLearn.nb_score_parts model goal_features "A")
    val ln3 = Math.ln 3.0
    val ln_three_halves = Math.ln 1.5
    val expected_prior = 30.0 * Math.ln 1001.0
    val expected_positive = ln3 * Math.ln (5.0 * 1000.0 / 1001.0)
    val expected_absent = 0.5 * ln3 * ~18.0
    val expected_negative = 0.2 * ln_three_halves * Math.ln
      (1.0 - 1000.0 / 1001.0)
    val scores = hhLearn.nb_scores model
      {pool = ["A", "not-in-model"], goal_features = goal_features}
  in
    expect "hhLearn trains exact self-prior and dependency counts"
      (hhLearn.nb_tfreq model "A" = SOME 1001 andalso
       hhLearn.nb_tfreq model "B" = SOME 1000 andalso
       hhLearn.nb_sfreq model "A" 1 = SOME 1000 andalso
       hhLearn.nb_sfreq model "A" 2 = SOME 1001 andalso
       hhLearn.nb_sfreq model "A" 3 = SOME 1);
    expect "hhLearn NB score has exact prior and positive terms"
      (learn_real_close expected_prior (#prior parts) andalso
       learn_real_close expected_positive (#positive parts));
    expect "hhLearn NB score has exact absent and negative terms"
      (learn_real_close expected_absent (#absent parts) andalso
       learn_real_close expected_negative (#negative parts) andalso
       learn_real_close
         (expected_prior + expected_positive + expected_absent +
          expected_negative) (#total parts));
    expect "hhLearn drops model-unknown goal features and scores pool only"
      (length scores = 1 andalso #1 (hd scores) = "A" andalso
       learn_real_close (#total parts) (#2 (hd scores)) andalso
       hhLearn.nb_rank model
         {pool = ["not-in-model", "A"], goal_features = goal_features,
          n = 2} = ["A"])
  end

val _ = test_hhLearn_nb_counts_and_scores ()

fun test_hhLearn_training_filters () =
  let
    val targets = List.tabulate (21, fn index =>
      learn_fact ("target" ^ Int.toString index) [index] false NONE)
    val target_names = map (fn (fact : hhLearn.fact_info) => #thmid fact)
      targets
    val source_twenty = learn_fact "source20" [100] false NONE
    val source_twenty_one = learn_fact "source21" [101] false NONE
    val size_model = learn_model
      (targets @ [source_twenty, source_twenty_one])
      (map (fn name => (name, [])) target_names @
       [("source20", List.take (target_names, 20)),
        ("source21", target_names)])
    val definition_model = learn_model
      [learn_fact "definition_target" [1] false NONE,
       learn_fact "definition_source" [2] true NONE]
      [("definition_target", []),
       ("definition_source", ["definition_target"])]
    val pure_conclusion = boolSyntax.mk_imp (boolSyntax.T, boolSyntax.T)
    val nonpure_conclusion = ``([] : bool list) = []``
    val pure_model = learn_model
      [learn_fact "pure" [1] false (SOME pure_conclusion),
       learn_fact "nonpure" [2] false (SOME nonpure_conclusion),
       learn_fact "uses" [3] false (SOME boolSyntax.T)]
      [("pure", []), ("nonpure", []),
       ("uses", ["pure", "nonpure"])]
    val broken_model = learn_model
      [learn_fact "intact_target" [1] false NONE,
       learn_fact "broken_source" [2] false NONE]
      [("intact_target", []),
       ("broken_source", ["intact_target", "missing"])]
  in
    expect "hhLearn trains 20 dependencies but self-trains over-20 proofs"
      (hhLearn.nb_tfreq size_model "target0" = SOME 1001 andalso
       hhLearn.nb_tfreq size_model "target19" = SOME 1001 andalso
       hhLearn.nb_tfreq size_model "target20" = SOME 1000 andalso
       hhLearn.nb_tfreq size_model "source21" = SOME 1000);
    expect "hhLearn def-stature facts train empty dependency lists"
      (hhLearn.nb_tfreq definition_model "definition_target" = SOME 1000);
    expect "hhLearn drops pure min/bool dependencies only"
      (hhLearn.pure_logic_concl pure_conclusion andalso
       not (hhLearn.pure_logic_concl nonpure_conclusion) andalso
       hhLearn.nb_tfreq pure_model "pure" = SOME 1000 andalso
       hhLearn.nb_tfreq pure_model "nonpure" = SOME 1001 andalso
       hhLearn.nb_sfreq pure_model "nonpure" 3 = SOME 1);
    expect "hhLearn dependency training requires an intact model path"
      (hhLearn.nb_tfreq broken_model "intact_target" = SOME 1000)
  end

val _ = test_hhLearn_training_filters ()

fun test_hhLearn_live_incomplete_dependencies () =
  let
    val prefix = Theory.current_theory () ^ "Theory."
    val bases = List.tabulate (21, fn index =>
      "hhLearn_dep_target_" ^ Int.toString index)
    fun save (name, theorem) =
      Feedback.quiet_messages Theory.save_thm (name, theorem)
    val targets = map (fn name => save
      (name, Thm.REFL (numSyntax.mk_suc
        (Term.mk_var (name, ``:num``))))) bases
    val small_name = "hhLearn_dep_small"
    val large_name = "hhLearn_dep_large"
    val small = save
      (small_name, Thm.CONJ (hd targets) (List.nth (targets, 1)))
    val large = save (large_name,
      foldl (fn (theorem, result) => Thm.CONJ result theorem)
        (hd targets) (tl targets))
    val names = map (fn name => prefix ^ name) bases
    val rows = map (fn name => (name, [1])) names @
      [(prefix ^ small_name, [2]), (prefix ^ large_name, [3])]
    val thmdata = (mlFeature.learn_tfidf rows, rows)
    val idf = hhLearn.create_idf_table rows
    fun model dependencies = hhLearn.train_nb_from_thmdata
      hhLearn.default_constants idf dependencies
      (hhStature.create_statures_for (Theory.current_theory ())) thmdata
    val originally_intact = #1 (mlThmData.intactdep_of_thm small) andalso
      #1 (mlThmData.intactdep_of_thm large)
    val intact_model = model (hhLearn.create_dep_table thmdata)
    val _ = Theory.delete_binding (List.nth (bases, 1))
    val dependencies = hhLearn.create_dep_table thmdata
    val broken_model = model dependencies
    val surviving = hd names
  in
    expect "hhLearn live intact proofs train up to the dependency limit"
      (originally_intact andalso
       length (Dep.depidl_of (Tag.dep_of (Thm.tag large))) = 21 andalso
       hhLearn.nb_tfreq intact_model surviving = SOME 1001);
    expect "hhLearn keeps fetchable dependencies of incomplete proofs"
      (not (#1 (mlThmData.intactdep_of_thm small)) andalso
       not (#1 (mlThmData.intactdep_of_thm large)) andalso
       hhLearn.dependencies_of dependencies (prefix ^ small_name) =
         SOME [surviving] andalso
       length (valOf (hhLearn.dependencies_of dependencies
         (prefix ^ large_name))) = 20);
    expect "hhLearn never trains truncated proofs, even with stale facts"
      (hhLearn.nb_tfreq broken_model surviving = SOME 1000 andalso
       hhLearn.nb_sfreq broken_model surviving 2 = NONE andalso
       hhLearn.nb_sfreq broken_model surviving 3 = NONE);
    List.app Theory.delete_binding
      (List.filter (fn name => name <> List.nth (bases, 1)) bases @
       [small_name, large_name])
  end

val _ = test_hhLearn_live_incomplete_dependencies ()

fun test_hhLearn_unselected_stale_fact () =
  let
    val primary = "arithmeticTheory.ADD1"
    val stale_base = "hhLearn_deleted_fact"
    val stale = Theory.current_theory () ^ "Theory." ^ stale_base
    val theorem = DB.fetch "arithmetic" "ADD1"
    val _ = Feedback.quiet_messages Theory.save_thm
      (stale_base, Thm.REFL boolSyntax.T)
    val goal = ([], Thm.concl theorem)
    val features = mlFeature.fea_of_goal true goal
    val rows = [(primary, features), (stale, [])]
    val thmdata = (mlFeature.learn_tfidf rows, rows)
    val _ = Theory.delete_binding stale_base
    val legacy = mlNearestNeighbor.thmknn_wdep thmdata 1 features
    val _ = hhLearn.clean_context_cache ()
    val context = hhLearn.create_context thmdata
  in
    expect "hhLearn skips missing facts when collecting dependencies"
      (hhLearn.dependencies_of (hhLearn.create_dep_table thmdata) stale =
       NONE);
    expect "hhLearn context tolerates unselected stale learning facts"
      (legacy = [primary] andalso
       hhLearn.rank context
         {filter = "knn", pool = NONE, goal = goal, n = 1} = legacy);
    hhLearn.clean_context_cache ()
  end

val _ = test_hhLearn_unselected_stale_fact ()

fun test_hhLearn_curves_and_mesh () =
  let
    val normalized = hhLearn.mesh_facts 2
      [(0.5, (ListPair.zip (["a", "b"], [100.0, 90.0]), [])),
       (0.5, (ListPair.zip (["b", "a"], [10.0, 1.0]), []))]
    val unknown_excluded = hhLearn.mesh_facts 2
      [(0.5, (ListPair.zip (["a", "b"], [1.0, 0.9]), [])),
       (0.5, ([("b", 1.0)], ["a"]))]
    val zero_penalty = hhLearn.mesh_facts 2
      [(0.5, ([("a", 1.0)], [])),
       (0.5, ([("c", 1.0)], ["a"]))]
    val insertion_order = hhLearn.mesh_facts 3
      [(0.5, (ListPair.zip (["a", "b"], [1.0, 1.0]), [])),
       (0.5, (ListPair.zip (["b", "c"], [1.0, 1.0]), []))]
    val fall_out_known = hhLearn.mesh_facts 3
      [(0.5, (hhLearn.weight_facts_steeply ["other", "fallout"], [])),
       (0.5, ([("recent", 1.0)], ["far_unknown"]))]
    fun alias_key "same_prop_alias" = "same_prop"
      | alias_key name = name
    val proposition_dedup = hhLearn.mesh_facts_by alias_key 3
      [(0.5, ([("same_prop", 1.0), ("left", 0.5)], [])),
       (0.5, ([("same_prop_alias", 1.0), ("right", 0.5)], []))]
    val proposition_unknown = hhLearn.mesh_facts_by alias_key 2
      [(0.5, ([("same_prop", 1.0)], [])),
       (0.5, ([("right", 1.0)], ["same_prop_alias"]))]
    fun is_induct name = name = "induct"
    val raw_mepo = ["induct", "a", "b"]
    val raw_mash = ["c", "d", "e"]
    val completed_first = hhLearn.mesh_facts 2
      [(0.5, (hhLearn.weight_facts_steeply
         (hhLearn.exclude_and_take is_induct 2 raw_mepo), [])),
       (0.5, (hhLearn.weight_facts_steeply
         (hhLearn.exclude_and_take is_induct 2 raw_mash), []))]
    val excluded_late = hhLearn.exclude_and_take is_induct 2
      (hhLearn.mesh_facts 2
        [(0.5, (hhLearn.weight_facts_steeply raw_mepo, [])),
         (0.5, (hhLearn.weight_facts_steeply raw_mash, []))])
  in
    expect "hhLearn ports the steep and smooth rank curves exactly"
      (learn_real_close 1.0 (hhLearn.steep_weight 0) andalso
       learn_real_close (0.62 * 0.62) (hhLearn.steep_weight 3) andalso
       learn_real_close (Math.pow (1.3, 15.5) + 15.0)
         (hhLearn.smooth_weight 0));
    expect "hhLearn mesh normalizes every channel by its top-N mean"
      (normalized = ["b", "a"]);
    expect "hhLearn mesh excludes unknowns from the score denominator"
      (unknown_excluded = ["a", "b"]);
    expect "hhLearn mesh penalizes known but unranked facts with zero"
      (zero_penalty = ["a", "c"]);
    expect "hhLearn mesh ports fold-union tie and dedup insertion order"
      (insertion_order = ["b", "c", "a"]);
    expect "hhLearn final mesh zero-penalizes proximity-channel fall-out"
      (fall_out_known = ["other", "recent", "fallout"]);
    expect "hhLearn mesh deduplicates alpha-equivalent proposition aliases"
      (proposition_dedup = ["same_prop", "right", "left"]);
    expect "hhLearn mesh excludes proposition aliases marked unknown"
      (proposition_unknown = ["same_prop", "right"]);
    expect "hhLearn mesh completes and refills each leg before combining"
      (length completed_first = 2 andalso length excluded_late = 1)
  end

val _ = test_hhLearn_curves_and_mesh ()

fun test_hhLearn_mash_channels () =
  let
    val filler = List.tabulate (100, fn index =>
      "known" ^ Int.toString index)
    val facts = "recent" :: filler @ ["chained"]
    val (ranking, remaining) = hhLearn.merge_mash_channels
      {max_facts = 4, suggestions = ["learner"], facts = facts,
       chained = ["chained"], unknown = ["recent", "chained"]}
  in
    expect "hhLearn channel merge keeps chained and proximity mechanisms"
      (ranking = ["chained", "recent", "learner"] andalso
       remaining = [])
  end

val _ = test_hhLearn_mash_channels ()

fun test_hhLearn_dispatch_cache_and_knn_anchor () =
  let
    val primary = "arithmeticTheory.ADD1"
    val secondary = "arithmeticTheory.ADD"
    val goal = ([], Thm.concl (DB.fetch "arithmetic" "ADD1"))
    val goal_features = mlFeature.fea_of_goal true goal
    val weights = Redblackmap.insertList
      (Redblackmap.mkDict Int.compare,
       map (fn feature => (feature, 1.0)) goal_features)
    val thmdata : mlThmData.thmdata =
      (weights, [(primary, goal_features), (secondary, [])])
    val _ = hhLearn.clean_context_cache ()
    val context = hhLearn.create_context thmdata
    val expected_knn = mlNearestNeighbor.thmknn_wdep thmdata 2
      goal_features
    val actual_knn = hhLearn.rank context
      {filter = "knn", pool = NONE, goal = goal, n = 2}
    val restricted_data : mlThmData.thmdata =
      (weights, [(secondary, [])])
    val expected_restricted_knn = mlNearestNeighbor.thmknn_wdep
      restricted_data 1 goal_features
    val restricted_knn = hhLearn.rank context
      {filter = "knn", pool = SOME [secondary], goal = goal, n = 1}
    val none = hhLearn.rank context
      {filter = "none", pool = NONE, goal = goal, n = 1}
    val mepo = hhLearn.rank context
      {filter = "mepo", pool = NONE, goal = goal, n = 1}
    val mash = hhLearn.rank context
      {filter = "mash", pool = NONE, goal = goal, n = 1}
    val mesh = hhLearn.rank context
      {filter = "mesh", pool = NONE, goal = goal, n = 1}
    val same_key_data : mlThmData.thmdata =
      (#1 mlThmData.empty_thmdata, [(secondary, [])])
    val cached = hhLearn.create_context same_key_data
    val local_name =
      "hhStatureTestTheory.hh_stature_registered_fixture"
    val changed_key_data : mlThmData.thmdata =
      (#1 mlThmData.empty_thmdata, [(local_name, [])])
    val changed = hhLearn.create_context changed_key_data
    val replaced = hhLearn.create_context same_key_data
    fun from_fixture names =
      List.all (fn name => name = primary orelse name = secondary) names
  in
    expect "hhLearn knn dispatch is byte-equal to thmknn_wdep"
      (actual_knn = expected_knn andalso
       restricted_knn = expected_restricted_knn);
    expect "hhLearn none dispatch preserves the full thmdata order"
      (none = [primary, secondary]);
    expect "hhLearn dispatches all three new filters on a live fixture"
      (mepo = [primary] andalso mash = [primary] andalso
       mesh = [primary] andalso from_fixture (mepo @ mash @ mesh));
    expect "hhLearn context cache uses the strong target fact inventory"
      (hhLearn.context_thmids cached = [secondary] andalso
       hhLearn.context_thmids changed = [local_name] andalso
       hhLearn.context_thmids replaced = [secondary]);
    expect "hhLearn uses exact 51/50 induction slack before exclusion"
      (hhLearn.over_request 50 = 51 andalso
       hhLearn.exclude_and_take (fn name => name = "induct") 50
         ("induct" :: List.tabulate (50, Int.toString)) =
       List.tabulate (50, Int.toString))
  end

val _ = test_hhLearn_dispatch_cache_and_knn_anchor ()

fun test_hhLearn_production_exclusion_and_mash () =
  let
    val induction = DB.fetch "list" "list_induction"
    val induction_base = "hhLearn_real_induction"
    val regular_bases = List.tabulate (101, fn index =>
      "hhLearn_regular_" ^ Int.toString index)
    fun regular_conclusion index = boolSyntax.mk_conj
      (Thm.concl induction,
       Term.mk_var
         ("hhLearn_marker_" ^ Int.toString index, Type.bool))
    (* Premises must be free of hypotheses, so fixtures are oracles. *)
    fun fixture conclusion =
      Thm.mk_oracle_thm "hhLearn_selftest" ([], conclusion)
    val regular_theorems = List.tabulate (101, fn index =>
      fixture (regular_conclusion index))
    fun save (name, theorem) =
      Feedback.quiet_messages Theory.save_thm (name, theorem)
    val _ = Feedback.quiet_messages Theory.save_thm
      (induction_base, fixture (Thm.concl induction))
    val _ = List.app (ignore o save)
      (ListPair.zip (regular_bases, regular_theorems))
    val prefix = Theory.current_theory () ^ "Theory."
    val induction_name = prefix ^ induction_base
    val regular_names = map (fn name => prefix ^ name) regular_bases
    val all_names = induction_name :: regular_names
    val direct_names = induction_name :: List.take (regular_names, 50)
    val goal = ([], regular_conclusion 0)
    val features = mlFeature.fea_of_goal true goal
    val rows = map (fn name => (name, features)) all_names
    val thmdata : mlThmData.thmdata =
      (mlFeature.learn_tfidf rows, rows)
    val _ = hhLearn.clean_context_cache ()
    val context = hhLearn.create_context thmdata
    fun ranked filter = hhLearn.rank context
      {filter = filter, pool = SOME direct_names, goal = goal, n = 50}
    val mepo = ranked "mepo"
    val mash = ranked "mash"
    val mesh = ranked "mesh"
    val knn = ranked "knn"
    val direct_rows = List.take (rows, 51)
    val direct_data : mlThmData.thmdata = (#1 thmdata, direct_rows)
    val expected_knn = mlNearestNeighbor.thmknn_wdep direct_data 50
      features
    val none = ranked "none"
    fun exact_regular ranking =
      length ranking = 50 andalso
      not (List.exists (fn name => name = induction_name) ranking) andalso
      Listsort.sort String.compare ranking =
        Listsort.sort String.compare (List.take (regular_names, 50))

    val model_rows = List.take (List.drop (rows, 1), 3)
    val model_data : mlThmData.thmdata =
      (mlFeature.learn_tfidf model_rows, model_rows)
    val dep_head = List.nth (regular_names, 3)
    val dep_one = List.nth (regular_names, 4)
    val dep_two = List.nth (regular_names, 5)
    val dependencies = hhLearn.dep_table_of (map
      (fn name =>
        (name, if name = dep_head then [dep_one, dep_two] else []))
      regular_names)
    val partial = hhLearn.make_context
      {thmdata = (mlFeature.learn_tfidf (tl rows), tl rows),
       model_thmdata = model_data, dependencies = dependencies}
    val details = hhLearn.mash_details partial
      {pool = NONE, goal = goal, max_facts = 2}
    val restricted_names = List.take (regular_names, 5)
    val restricted = hhLearn.mash_details partial
      {pool = SOME restricted_names, goal = goal, max_facts = 2}
    val partial_mesh = hhLearn.rank partial
      {filter = "mesh", pool = NONE, goal = goal, n = 2}
    val invalid_filter =
      (ignore (hhLearn.rank context
        {filter = "bogus", pool = NONE, goal = goal, n = 1}); false)
      handle Feedback.HOL_ERR _ => true
  in
    expect "hhLearn mepo rank excludes induction with refill"
      (exact_regular mepo);
    expect "hhLearn mash rank excludes induction with refill"
      (exact_regular mash);
    expect "hhLearn mesh rank excludes induction with refill"
      (exact_regular mesh);
    expect "hhLearn production rank leaves knn and none untouched"
      (knn = expected_knn andalso
       List.exists (fn name => name = induction_name) knn andalso
       none = direct_names);
    expect "hhLearn mash uses observable 2n+25 learner depth"
      (#max_suggestions details = 29 andalso
       length (#learner details) = 29);
    expect "hhLearn mash meshes NB with pool kNN"
      (List.take (#learner details, 5) =
       [List.nth (regular_names, 0), List.nth (regular_names, 100),
        List.nth (regular_names, 99), List.nth (regular_names, 98),
        List.nth (regular_names, 97)]);
    expect "hhLearn mash expands dependencies in order before cutting"
      (#ranking details = [dep_head, dep_one] andalso
       #unknown details = [List.last regular_names]);
    expect "hhLearn mash restricts both learner engines to the pool"
      (#max_suggestions restricted = 29 andalso
       length (#learner restricted) = 5 andalso
       List.all
         (fn name => List.exists (fn allowed => allowed = name)
           restricted_names)
         (#learner restricted) andalso
       #ranking restricted = [dep_head, dep_one]);
    expect "hhLearn final mesh uses the partial-model unknown remainder"
      (partial_mesh = [List.last regular_names, dep_head]);
    expect "hhLearn rank rejects unknown filter names"
      invalid_filter
  end

val _ = test_hhLearn_production_exclusion_and_mash ()

fun same_thmdata ((left_weights, left_features) : mlThmData.thmdata,
    (right_weights, right_features) : mlThmData.thmdata) =
  let
    fun same_weight ((left_key, left), (right_key, right)) =
      left_key = right_key andalso Real.== (left, right)
    fun all_pairs _ [] [] = true
      | all_pairs same (left :: lefts) (right :: rights) =
          same (left, right) andalso all_pairs same lefts rights
      | all_pairs _ _ _ = false
  in
    left_features = right_features andalso
    all_pairs same_weight (Redblackmap.listItems left_weights)
      (Redblackmap.listItems right_weights)
  end

fun test_hhLearn_target_thmdata () =
  let
    val _ = hhLearn.clean_context_cache ()
    val ambient = Theory.current_theory ()
    val legacy = mlThmData.create_thmdata ()
    val explicit = hhLearn.create_thmdata_for ambient
    val explicit_again = hhLearn.create_thmdata_for ambient
    val ambient_cache_size = hhLearn.target_thmdata_cache_size ()
    val ambient_builds = hhLearn.target_thmdata_cache_builds ()
    val before_data = hhLearn.create_thmdata_for "list"
    val list_builds = hhLearn.target_thmdata_cache_builds ()
    val _ = Feedback.quiet_messages Theory.new_theory
      "hhLearnUnrelatedAmbientTest"
    val unrelated = boolSyntax.new_definition
      ("unrelated_definition", boolSyntax.mk_eq
        (Term.mk_var ("unrelated_constant", Type.bool), boolSyntax.T))
    val _ = Theory.save_thm ("unrelated_theorem", unrelated)
    val after_data = hhLearn.create_thmdata_for "list"
    val unchanged_list_builds = hhLearn.target_thmdata_cache_builds ()
    val arithmetic_data = hhLearn.create_thmdata_for "arithmetic"
    val alternating_data = hhLearn.create_thmdata_for "list"
    val alternating_builds = hhLearn.target_thmdata_cache_builds ()
    val final_cache_size = hhLearn.target_thmdata_cache_size ()
    val _ = ignore arithmetic_data
  in
    expect "target thmdata is byte-equivalent for the ambient target"
      (same_thmdata (legacy, explicit) andalso
       same_thmdata (explicit, explicit_again));
    expect "target thmdata cache is a bounded one-entry replacement cache"
      (ambient_cache_size = 1 andalso ambient_builds = 1 andalso
       final_cache_size = 1);
    expect "target thmdata is independent of unrelated ambient theory"
      (same_thmdata (before_data, after_data) andalso
       list_builds = unchanged_list_builds);
    expect "target thmdata cache invalidates on alternating targets"
      (same_thmdata (before_data, alternating_data) andalso
       alternating_builds = unchanged_list_builds + 2)
  end

val _ = test_hhLearn_target_thmdata ()

(* A theorem with hypotheses is no premise.  Exported by its bare
   conclusion, [F] |- F hands the provers a false axiom (ContradictoryAxioms,
   bogus proofs Metis then rejects); discharged, it is unusable by replay. *)
fun test_hypothesis_premises () =
  let
    val base = "hh_hypothesis_fixture"
    val theory = Theory.current_theory ()
    val fixture = theory ^ "Theory." ^ base
    val closed = theory ^ "Theory.unrelated_theorem"
    val truth = "boolTheory.TRUTH"
    val _ = Feedback.quiet_messages Theory.save_thm
      (base, Thm.ASSUME boolSyntax.F)
    val _ = hhLearn.clean_context_cache ()
    val target_names = map #1 (#2 (hhLearn.create_thmdata_for theory))
    val goal = ([], boolSyntax.T)
    val features = mlFeature.fea_of_goal true goal
    val rows = [(truth, features), (fixture, features)]
    val context =
      hhLearn.create_context (mlFeature.learn_tfidf rows, rows)
    val none = hhLearn.rank context
      {filter = "none", pool = NONE, goal = goal, n = 2}
    val root = hhSchedule.new_problem_dir (hhConfig.state_dir ())
    val options : hhConfig.hh_options =
      {timeout = 30, max_proofs = 1, provers = [Eprover], slices = 1,
       cores = 1,
       export_workers = 1,
       filter = "none", max_facts = NONE, format = "", type_enc = "",
       lam_trans = "", mono_iters = 3, mono_instances = NONE,
       minimize = true, preplay_timeout = 1.0, minimize_timeout = 1.0,
       cache = false, cache_dir = "", cache_max_entries = 100,
       debug_dir = NONE,
       preplay_drop_one = false, verbose = false}
    fun slice type_enc lam_trans : hhProver.slice =
      {prover = Eprover, format = "fof", type_enc = type_enc,
       lam_trans = lam_trans, nfacts = 0, filter = "none",
       extra_opts = [], slice_size = 1}
    val slices = [slice "" "", slice "mono_guards" "lifting"]
    fun export ranking =
      (hhSchedule.export_problems root options goal [("none", ranking)]
         (map (fn s => (prover Eprover, s)) slices);
       map (String.concat o read_lines o hhSchedule.problem_path root)
         slices)
    val with_fixture = export [truth, fixture]
    val without_fixture = export [truth]
  in
    expect "target thmdata skips theorems with hypotheses"
      (List.exists (fn name => name = closed) target_names andalso
       not (List.exists (fn name => name = fixture) target_names));
    expect "premise ranking skips theorems with hypotheses"
      (hhLearn.context_thmids context = [truth] andalso none = [truth]);
    expect "legacy and generated exports drop theorems with hypotheses"
      (with_fixture = without_fixture);
    remove_tree root;
    Theory.delete_binding base;
    hhLearn.clean_context_cache ()
  end

val _ = test_hypothesis_premises ()

local open hhReconstruct hhTranslate holyHammer hhExportLib hhExportFof
  hhExportTf0 hhExportTh0 hhExportTf1 hhExportTh1 hhConfig hhProver hhSlice
  hhCache hhSchedule hhStature hhMePo hhLearn
in end
