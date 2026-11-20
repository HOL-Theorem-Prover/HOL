(* ========================================================================= *)
(* FILE          : hhConfig.sml                                              *)
(* DESCRIPTION   : HolyHammer configuration and executable discovery         *)
(* ========================================================================= *)

structure hhConfig :> hhConfig =
struct

datatype prover = Eprover | Vampire | Zipperposition | Z3

val all_provers = [Eprover, Vampire, Zipperposition, Z3]

fun prover_name Eprover = "e"
  | prover_name Vampire = "vampire"
  | prover_name Zipperposition = "zipperposition"
  | prover_name Z3 = "z3"

fun prover_of_name name =
  List.find (fn prover => prover_name prover = name) all_provers

fun prover_compare (left, right) =
  String.compare (prover_name left, prover_name right)

type hh_options =
  {timeout : int,
   max_proofs : int,
   provers : prover list,
   slices : int,
   cores : int,
   export_workers : int,
   filter : string,
   max_facts : int option,
   format : string,
   type_enc : string,
   lam_trans : string,
   mono_iters : int,
   mono_instances : int option,
   minimize : bool,
   preplay_timeout : real,
   minimize_timeout : real,
   preplay_drop_one : bool,
   cache : bool,
   cache_dir : string,
   cache_max_entries : int,
   debug_dir : string option,
   verbose : bool}

val ERR = Feedback.mk_HOL_ERR "hhConfig"

fun join a b = OS.Path.concat (a, b)

fun is_dir path = OS.FileSys.isDir path handle OS.SysErr _ => false

fun readable path =
  OS.FileSys.access (path, [OS.FileSys.A_READ])
  handle OS.SysErr _ => false

fun executable path =
  OS.FileSys.access (path, [OS.FileSys.A_READ, OS.FileSys.A_EXEC]) andalso
  not (is_dir path)
  handle OS.SysErr _ => false

fun ensure_dir path =
  if path = "" orelse is_dir path then ()
  else
    let
      val parent = OS.Path.dir path
      val _ =
        if parent = "" orelse parent = path then () else ensure_dir parent
    in
      OS.FileSys.mkDir path
      handle OS.SysErr _ =>
        if is_dir path then () else raise Fail ("cannot create " ^ path)
    end

val temp_counter = Portable.make_counter {init = 0, inc = 1}

fun remove_quietly path = OS.FileSys.remove path handle OS.SysErr _ => ()

(* The PID alone is not fresh under Poly, hence the counter. *)
fun temp_path path =
  path ^ "." ^ Portable.unique_tmp_suffix () ^ "." ^
  Int.toString (temp_counter ()) ^ ".tmp"

fun commit {temporary, final} =
  OS.FileSys.rename {old = temporary, new = final}
  handle OS.SysErr _ =>
    (remove_quietly final;
     OS.FileSys.rename {old = temporary, new = final})

(* The temporary is opened and closed inside Portable.bracket, so that an
   interrupt cannot leave the stream open, and removed on any exception
   (also one that arrives as the bracket returns). *)
fun stage_to {open_out, close_out} temporary write =
  let
    fun release output = (close_out output handle _ => ())
    fun body output =
      let val result = write output in (close_out output; result) end
  in
    Portable.bracket (fn () => open_out temporary) release body
    handle exn => (remove_quietly temporary; raise exn)
  end

fun stage_write io path write =
  let val temporary = temp_path path in
    (temporary, stage_to io temporary write)
  end

fun write_atomically io path write =
  let val (temporary, result) = stage_write io path write in
    (commit {temporary = temporary, final = path}; result)
    handle exn => (remove_quietly temporary; raise exn)
  end

(* Best effort: errors are ignored, and a symbolic link is removed rather
   than followed, so only files below path itself are deleted. *)
fun remove_tree path =
  let
    val link = OS.FileSys.isLink path handle OS.SysErr _ => false
  in
    if not link andalso is_dir path then
      let
        val stream = OS.FileSys.openDir path
        fun loop names =
          case OS.FileSys.readDir stream of
              NONE => names
            | SOME name => loop (name :: names)
        val names =
          (loop [] handle error => (OS.FileSys.closeDir stream; raise error))
        val _ = OS.FileSys.closeDir stream
      in
        List.app (fn name => remove_tree (join path name)) names;
        OS.FileSys.rmDir path
      end
    else OS.FileSys.remove path
  end
  handle OS.SysErr _ => ()

(* HHCONFIG_TEST_ROOT is used only by the hermetic selftest. *)
fun test_root () = OS.Process.getEnv "HHCONFIG_TEST_ROOT"

fun home_dir () =
  case test_root () of
      SOME root => join root "home"
    | NONE =>
      (case OS.Process.getEnv "HOME" of
           SOME home => home
         | NONE => raise Fail "HOME is not set")

fun holdir () =
  case test_root () of
      SOME root => join root "holdir"
    | NONE => Option.getOpt (OS.Process.getEnv "HOLDIR", Globals.HOLDIR)

fun state_dir () =
  let
    val dir =
      case OS.Process.getEnv "HOL4_HAMMER_DIR" of
          SOME path => path
        | NONE => join (join (home_dir ()) ".hol4") "hammer"
    val _ = ensure_dir dir
  in
    dir
  end

fun trim_left s =
  Substring.string (Substring.dropl Char.isSpace (Substring.full s))

fun trim s =
  Substring.string (Substring.dropr Char.isSpace
    (Substring.dropl Char.isSpace (Substring.full s)))

fun before_comment s =
  Substring.string (#1 (Substring.splitl (fn c => c <> #"#")
    (Substring.full s)))

fun split_assignment s =
  let
    val (key, rest) = Substring.splitl (fn c => c <> #"=") (Substring.full s)
  in
    if Substring.isEmpty rest then NONE
    else
      let
        val key = trim (Substring.string key)
        val value = trim (Substring.string (Substring.triml 1 rest))
      in
        if key = "" then NONE else SOME (key, value)
      end
  end

fun read_config path =
  if not (readable path) then []
  else
    let
      val input = TextIO.openIn path
      fun loop acc =
        case TextIO.inputLine input of
            NONE => List.rev acc
          | SOME line =>
            let
              val item = split_assignment (before_comment line)
            in
              loop (case item of NONE => acc | SOME x => x :: acc)
            end
      val result = loop []
      val _ = TextIO.closeIn input
    in
      result
    end

fun lookup key [] = NONE
  | lookup key ((key', value) :: rest) =
      if key = key' then SOME value else lookup key rest

fun member key entries = Option.isSome (lookup key entries)

fun first_hits entries =
  let
    fun loop seen [] = List.rev seen
      | loop seen ((key, value) :: rest) =
          if member key seen then loop seen rest
          else loop (seen @ [(key, value)]) rest
  in
    loop [] entries
  end

fun config_entries () =
  let
    val user = join (join (home_dir ()) ".hol4") "hammer/config"
    val system = read_config (join (join (holdir ()) "etc") "hammer-config")
  in
    first_hits (read_config user @ system)
  end

fun default_eval_dir () =
  join (join (join (holdir ()) "src") "holyhammer") "eval"

type option_spec =
  {name : string,
   default : unit -> string,
   expected : string,
   doc : string,
   valid : string -> bool}

fun int_value value =
  case Int.scan StringCvt.DEC Substring.getc
        (Substring.full (trim value)) of
      SOME (number, rest) =>
        if Substring.size rest = 0 then SOME number else NONE
    | NONE => NONE

fun real_value value =
  case Real.scan Substring.getc (Substring.full (trim value)) of
      SOME (number, rest) =>
        if Substring.size rest = 0 then SOME number else NONE
    | NONE => NONE

fun bool_value value =
  case String.map Char.toLower (trim value) of
      "true" => SOME true
    | "yes" => SOME true
    | "on" => SOME true
    | "1" => SOME true
    | "false" => SOME false
    | "no" => SOME false
    | "off" => SOME false
    | "0" => SOME false
    | _ => NONE

fun positive_int value =
  case int_value value of SOME number => number > 0 | NONE => false

fun nonnegative_int value =
  case int_value value of SOME number => number >= 0 | NONE => false

fun positive_real value =
  case real_value value of
      SOME number => Real.isFinite number andalso number > 0.0
    | NONE => false

fun optional_positive_int value =
  trim value = "" orelse positive_int value

fun valid_format value =
  trim value = "" orelse hhTypeEnc.valid_format (trim value)

fun valid_type_enc value =
  (ignore (hhTypeEnc.of_string (trim value)); true) handle Fail _ => false

fun valid_lam_trans value =
  trim value = "" orelse hhLamTrans.valid_mode (trim value)

fun one_of choices value =
  List.exists (fn choice => trim value = choice) choices

fun valid_filter value =
  one_of ["", "knn", "mepo", "mash", "mesh", "none"] value

fun parse_provers value =
  case String.tokens Char.isSpace (trim value) of
      [] => NONE
    | names =>
        let val provers = List.mapPartial prover_of_name names in
          if length provers = length names then SOME provers else NONE
        end

val valid_provers = Option.isSome o parse_provers

val default_export_workers = 2

(* The default of the preplay_timeout option, in seconds. *)
val default_preplay_timeout = 2.5

val option_specs : option_spec list =
  [{name = "timeout", default = fn () => "30",
    expected = "a positive integer",
    doc = "wall-clock budget of the proof search in seconds, counted from " ^
          "the launch of the provers (the export of the problems is " ^
          "charged to it only where it overlaps the search: see " ^
          "hhSchedule.export_mode); the proofs found are reconstructed " ^
          "until max_proofs verify before the timeout, or one verifies " ^
          "after it, so a call can return after the timeout, and " ^
          "minimisation stops at it",
    valid = positive_int},
   {name = "max_proofs", default = fn () => "4",
    expected = "a positive integer",
    doc = "maximum number of reconstructed proofs", valid = positive_int},
   {name = "provers", default = fn () => "e vampire zipperposition",
    expected = "a nonempty space-separated list of prover names: " ^
      String.concatWith ", " (map prover_name all_provers),
    doc = "provers eligible for scheduling", valid = valid_provers},
   {name = "slices", default = fn () => "0",
    expected = "a non-negative integer",
    doc = "schedule length (0 means 24 times cores)",
    valid = nonnegative_int},
   {name = "cores", default = fn () => "0",
    expected = "a non-negative integer",
    doc = "worker count (0 means detected processor count)",
    valid = nonnegative_int},
   {name = "export_workers",
    default = fn () => Int.toString default_export_workers,
    expected = "a non-negative integer",
    doc = "threads that finish generated problems (1 means inline on " ^
          "the calling thread, 0 means cores; at most cores)",
    valid = nonnegative_int},
   {name = "filter", default = fn () => "",
    expected = "empty, knn, mepo, mash, mesh, or none",
    doc = "schedule-wide premise filter override (empty means per-slice)",
    valid = valid_filter},
   {name = "max_facts", default = fn () => "",
    expected = "empty or a positive integer",
    doc = "fact cap (empty means the per-slice default)",
    valid = optional_positive_int},
   {name = "format", default = fn () => "",
    expected = "empty or a supported TPTP format",
    doc = "schedule-wide format override (empty means per-slice)",
    valid = valid_format},
   {name = "type_enc", default = fn () => "",
    expected = "empty or a supported type encoding",
    doc = "schedule-wide type encoding override (empty means per-slice)",
    valid = valid_type_enc},
   {name = "lam_trans", default = fn () => "",
    expected = "empty or a supported lambda translation",
    doc = "schedule-wide lambda translation override (empty means per-slice)",
    valid = valid_lam_trans},
   {name = "mono_iters", default = fn () => "3",
    expected = "a positive integer", doc = "monomorphization rounds",
    valid = positive_int},
   {name = "mono_instances", default = fn () => "",
    expected = "empty or a positive integer",
    doc = "new monomorphization-instance cap (empty: the slice's fact " ^
          "count, at least the prover's own cap)",
    valid = optional_positive_int},
   {name = "minimize", default = fn () => "true",
    expected = "a Boolean (true/false, yes/no, on/off, or 1/0)",
    doc = "minimize reconstructed proofs", valid = Option.isSome o bool_value},
   {name = "preplay_timeout",
    default = fn () => Real.toString default_preplay_timeout,
    expected = "a positive real number",
    doc = "time limit for each replay of a proof, in seconds",
    valid = positive_real},
   {name = "minimize_timeout", default = fn () => "1.0",
    expected = "a positive real number",
    doc = "time limit for each minimization attempt, in seconds",
    valid = positive_real},
   {name = "preplay_drop_one", default = fn () => "true",
    expected = "a Boolean (true/false, yes/no, on/off, or 1/0)",
    doc = "while no new lemma list waits, retry each list Metis could " ^
          "not replay without one of its lemmas",
    valid = Option.isSome o bool_value},
   {name = "cache", default = fn () => "false",
    expected = "a Boolean (true/false, yes/no, on/off, or 1/0)",
    doc = "enable the result cache", valid = Option.isSome o bool_value},
   {name = "cache_dir", default = fn () => join (state_dir ()) "cache",
    expected = "a nonempty path", doc = "result cache directory",
    valid = fn value => trim value <> ""},
   {name = "cache_max_entries", default = fn () => "100000",
    expected = "a positive integer", doc = "maximum cached result count",
    valid = positive_int},
   {name = "debug_dir", default = fn () => "",
    expected = "a path or empty",
    doc = "directory for retained problems and prover output",
    valid = fn _ => true},
   {name = "verbose", default = fn () => "false",
    expected = "a Boolean (true/false, yes/no, on/off, or 1/0)",
    doc = "report every prover slice as it starts and ends",
    valid = Option.isSome o bool_value}]

val defaults =
  ("eval.dir", default_eval_dir) ::
  map (fn ({name, default, ...} : option_spec) => (name, default)) option_specs

val runtime = ref ([] : (string * string) list)

fun default key =
  case List.find (fn (key', _) => key = key') defaults of
      NONE => NONE
    | SOME (_, value) => SOME (value ())

fun env_name key =
  "HOL4_HAMMER_" ^
  String.map (fn c =>
    if c = #"." then #"_" else Char.toUpper c) key

(* Callers that resolve many keys pass the config entries they read once;
   reading them lazily keeps runtime-set keys from touching the disk. *)
fun value_with_source_in entries key =
  case lookup key (!runtime) of
      SOME value => SOME (value, "set")
    | NONE =>
      (case lookup key (entries ()) of
           SOME value => SOME (value, "config")
         | NONE =>
           (case OS.Process.getEnv (env_name key) of
                SOME value => SOME (value, "environment")
              | NONE =>
                (case default key of
                     SOME value => SOME (value, "default")
                   | NONE => NONE)))

fun value_with_source key = value_with_source_in config_entries key

fun read_config_once () =
  let val entries = config_entries () in fn () => entries end

val queried = ref ([] : string list)

fun remember key =
  if List.exists (fn key' => key = key') (!queried) then ()
  else queried := !queried @ [key]

fun get key =
  let val _ = remember key
  in Option.map #1 (value_with_source key) end

fun get_int key =
  case get key of
      NONE => NONE
    | SOME value => Int.fromString (trim value)

fun get_bool key = Option.mapPartial bool_value (get key)

fun get_path key =
  case get key of
      SOME "~" => SOME (home_dir ())
    | SOME value =>
      if String.isPrefix "~/" value then
        SOME (join (home_dir ())
                    (String.extract (value, 2, NONE)))
      else SOME value
    | NONE => NONE

fun unique [] = []
  | unique (x :: xs) =
      if List.exists (fn y => x = y) xs then unique xs else x :: unique xs

fun dump () =
  let
    val entries = read_config_once ()
    val config_keys = map #1 (entries ())
    val default_keys = map #1 defaults
    val keys = unique (config_keys @ default_keys @ !queried)
    fun render key =
      case value_with_source_in entries key of
          NONE => NONE
        | SOME (value, source) => SOME (key, source ^ ": " ^ value)
  in
    List.mapPartial render keys
  end

fun option_spec key =
  List.find (fn ({name, ...} : option_spec) => name = key) option_specs

fun valid_keys () =
  String.concatWith ", "
    (map (fn ({name, expected, ...} : option_spec) =>
       name ^ " (" ^ expected ^ ")") option_specs)

fun unknown_option caller key =
  raise ERR caller
    ("unknown HolyHammer option '" ^ key ^ "'; valid keys: " ^ valid_keys ())

fun checked_spec caller key =
  case option_spec key of
      SOME spec => spec
    | NONE => unknown_option caller key

fun invalid_value caller key value expected =
  raise ERR caller
    ("invalid value '" ^ value ^ "' for HolyHammer option '" ^ key ^
     "'; expected " ^ expected ^ "; valid keys: " ^ valid_keys ())

fun check_value caller
      ({name, expected, valid, ...} : option_spec) value =
  if valid value then () else invalid_value caller name value expected

fun remove_key key entries =
  List.filter (fn (key', _) => key <> key') entries

fun hh_set (key, value) =
  let
    val spec = checked_spec "hh_set" key
    val _ = check_value "hh_set" spec value
  in
    runtime := (key, value) :: remove_key key (!runtime)
  end

fun hh_unset key =
  let val _ = checked_spec "hh_unset" key
  in runtime := remove_key key (!runtime) end

fun effective_option_in entries ({name, default, ...} : option_spec) =
  case value_with_source_in entries name of
      SOME result => result
    | NONE => (default (), "default")

fun effective_option spec = effective_option_in config_entries spec

fun hh_get key =
  let
    val spec = checked_spec "hh_get" key
    val (value, _) = effective_option spec
  in
    value
  end

fun parameter_source "environment" = "env"
  | parameter_source source = source

fun hh_params () =
  let val entries = read_config_once () in
    map (fn (spec as {name, ...} : option_spec) =>
      let val (value, source) = effective_option_in entries spec
      in (name, value, parameter_source source) end) option_specs
  end

fun print_params () =
  let
    fun print_one ((key, value, source), {doc, ...} : option_spec) =
      print (key ^ " = " ^ value ^ " (" ^ source ^ ") -- " ^ doc ^ "\n")
  in
    List.app print_one (ListPair.zip (hh_params (), option_specs))
  end


fun optional_string value =
  if trim value = "" then NONE else SOME value

fun detected_cores () =
  Int.max
    (case Thread.numPhysicalProcessors () of
         SOME number => number
       | NONE => Thread.numProcessors (), 1)

(* [overrides] take precedence over every other source, without touching
   the runtime settings that hh_set changes. *)
fun snapshot_with overrides =
  let
    val entries = read_config_once ()
    fun required key parse =
      let
        val spec = checked_spec "snapshot" key
        val value =
          case lookup key overrides of
              SOME value => value
            | NONE => #1 (effective_option_in entries spec)
        val _ = check_value "snapshot" spec value
      in
        case parse value of
            SOME result => result
          | NONE => invalid_value "snapshot" key value (#expected spec)
      end
    fun optional_int value =
      if trim value = "" then SOME NONE
      else Option.map SOME (int_value value)
    val _ = List.app (fn (key, _) => ignore (checked_spec "snapshot" key))
      overrides
    val timeout = required "timeout" int_value
    val max_proofs = required "max_proofs" int_value
    val provers = required "provers" parse_provers
    val configured_slices = required "slices" int_value
    val configured_cores = required "cores" int_value
    val cores = if configured_cores = 0 then detected_cores ()
                else configured_cores
    val configured_workers = required "export_workers" int_value
    val export_workers =
      Int.min (cores, if configured_workers = 0 then cores
                      else configured_workers)
    val slices = if configured_slices = 0 then 24 * cores
                 else configured_slices
    val filter = required "filter" (SOME o trim)
    val max_facts = required "max_facts" optional_int
    val format = required "format" (SOME o trim)
    val type_enc = required "type_enc" (SOME o trim)
    val lam_trans = required "lam_trans" (SOME o trim)
    val mono_iters = required "mono_iters" int_value
    (* NONE means "no explicit cap": the per-prover value wins. *)
    val mono_instances = required "mono_instances" optional_int
    val minimize = required "minimize" bool_value
    val preplay_timeout = required "preplay_timeout" real_value
    val minimize_timeout = required "minimize_timeout" real_value
    val preplay_drop_one = required "preplay_drop_one" bool_value
    val cache = required "cache" bool_value
    val cache_dir = required "cache_dir" SOME
    val cache_max_entries = required "cache_max_entries" int_value
    val debug_dir = required "debug_dir" (SOME o optional_string)
    val verbose = required "verbose" bool_value
  in
    {timeout = timeout, max_proofs = max_proofs, provers = provers,
     slices = slices, cores = cores,
     export_workers = export_workers, filter = filter,
     max_facts = max_facts, format = format, type_enc = type_enc,
     lam_trans = lam_trans, mono_iters = mono_iters,
     mono_instances = mono_instances, minimize = minimize,
     preplay_timeout = preplay_timeout,
     minimize_timeout = minimize_timeout,
     preplay_drop_one = preplay_drop_one, cache = cache,
     cache_dir = cache_dir, cache_max_entries = cache_max_entries,
     debug_dir = debug_dir, verbose = verbose}
  end

fun snapshot () = snapshot_with []

fun uname key =
  case List.find (fn (key', _) => key = key') (Posix.ProcEnv.uname ()) of
      SOME (_, value) => value
    | NONE => ""

fun lower s = String.map Char.toLower s

fun platform () =
  let
    val machine = lower (uname "machine")
    val system = lower (uname "sysname")
    val arch =
      if machine = "x86_64" orelse machine = "amd64" then "x86_64"
      else if machine = "aarch64" orelse machine = "arm64" then "arm64"
      else machine
  in
    arch ^ "-" ^ system
  end

fun path_exec names =
  let
    fun direct name =
      if String.isSubstring "/" name then
        if executable name then SOME name else NONE
      else NONE
    fun in_dir dir name =
      let val path = join dir name
      in if executable path then SOME path else NONE end
    fun on_path name =
      case direct name of
          SOME path => SOME path
        | NONE =>
          (case OS.Process.getEnv "PATH" of
               NONE => NONE
             | SOME path =>
               Portable.get_first (fn dir => in_dir
                 (if dir = "" then "." else dir) name)
                 (String.fields (fn c => c = #":") path))
  in
    Portable.get_first on_path names
  end

fun all_digits s =
  String.size s > 0 andalso
  List.all Char.isDigit (String.explode s)

fun without_zeroes s =
  let
    fun first i =
      if i + 1 < String.size s andalso String.sub (s, i) = #"0" then
        first (i + 1)
      else i
  in
    String.extract (s, first 0, NONE)
  end

fun token_compare (left, right) =
  if all_digits left andalso all_digits right then
    let
      val left' = without_zeroes left
      val right' = without_zeroes right
    in
      case Int.compare (String.size left', String.size right') of
          EQUAL => String.compare (left', right')
        | order => order
    end
  else String.compare (left, right)

fun version_compare (left, right) =
  let
    val left_tokens = String.tokens (not o Char.isAlphaNum) left
    val right_tokens = String.tokens (not o Char.isAlphaNum) right
  in
    List.collate token_compare (left_tokens, right_tokens)
  end

fun insert_version item [] = [item]
  | insert_version (item as (version, _))
      ((head as (head_version, _)) :: rest) =
      if version_compare (version, head_version) = GREATER then
        item :: head :: rest
      else head :: insert_version item rest

fun sort_versions versions =
  List.foldl (fn (item, result) => insert_version item result) [] versions

fun directory_names path =
  let
    val stream = OS.FileSys.openDir path
    fun loop names =
      case OS.FileSys.readDir stream of
          NONE => List.rev names
        | SOME name => loop (name :: names)
    val names = loop []
    val _ = OS.FileSys.closeDir stream
  in
    names
  end
  handle OS.SysErr _ => []

fun install_exec root prover names =
  let
    val prefix = prover ^ "-"
    fun candidate name =
      String.isPrefix prefix name andalso is_dir (join root name)
    fun version name = String.extract (name, String.size prefix, NONE)
    val versions =
      sort_versions (map (fn name => (version name, name))
                         (List.filter candidate (directory_names root)))
    val plat = platform ()
    fun in_version (_, name) = path_exec_in (join (join root name) plat) names
  in
    case Portable.get_first in_version versions of
        SOME path => SOME path
      (* Legacy flat layout: the binary sits directly in provers/, as the
         pre-download-provers instructions told users to install it. *)
      | NONE => path_exec_in root names
  end

and path_exec_in dir names =
  if is_dir dir then
    Portable.get_first (fn name =>
      let val path = join dir name
      in if executable path then SOME path else NONE end) names
  else NONE

fun find_exec prover env_var names =
  let
    val config_key = "prover." ^ prover ^ ".executable"
    fun configured () =
      case lookup config_key (config_entries ()) of
          SOME path => if executable path then SOME path else NONE
        | NONE => NONE
    fun environment () =
      case OS.Process.getEnv env_var of
          SOME path => if executable path then SOME path else NONE
        | NONE => NONE
    fun installed root = install_exec root prover names
    fun system_install () =
      installed (join (join (join (holdir ()) "src") "holyhammer") "provers")
    fun state_install () = installed (join (state_dir ()) "provers")
    fun user_install () =
      installed (join (join (join (home_dir ()) ".hol4") "hammer")
                 "provers")
  in
    Portable.get_first (fn source => source ())
      [configured, environment, fn () => path_exec names,
       system_install, state_install, user_install]
  end

end
