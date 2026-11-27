(* ========================================================================= *)
(* FILE          : hhProver.sml                                              *)
(* DESCRIPTION   : HolyHammer prover configurations and output parsers       *)
(* AUTHOR        : Lukasz Czajka                                             *)
(* BASED ON      : Isabelle's sledgehammer_atp_systems.ML (Fabian Immler,    *)
(*                 Jasmin Blanchette, Martin Desharnais), for the prover     *)
(*                 options, the SZS statuses, and the monomorphisation       *)
(*                 limits.                                                   *)
(* ========================================================================= *)

structure hhProver :> hhProver =
struct

open aiLib

datatype prover = datatype hhConfig.prover

datatype szs =
    SzsTheorem
  | SzsCounterSat
  | SzsSatisfiable
  | SzsGaveUp
  | SzsTimeout
  | SzsResourceOut
  | SzsInappropriate
  | SzsUnknown of string
  | RunFailure of string

type slice =
  {prover : prover, format : string, type_enc : string,
   lam_trans : string, nfacts : int, filter : string,
   extra_opts : string list, slice_size : int}

type run_request =
  {timeout : int, problem : string, extra : string list,
   debug_dir : string option}

type run_result =
  {szs : szs, used_axioms : string list option, time : real,
   version : string option, output_file : string}

type running =
  {kill : unit -> unit,
   wait : unit -> run_result}

type prover_config =
  {name : string,
   exec_names : string list,
   env_var : string,
   version_args : string list,
   parse_version : string -> string option,
   tested_versions : string list,
   supported_formats : string list,
   mk_command : string -> run_request -> string * string list,
   parse_output : string list -> szs * string list option,
   mono_instances : int,
   slices : slice list,
   legacy : bool}

val trim = hhConfig.trim
fun first_word text =
  Substring.string (Substring.takel (not o Char.isSpace)
    (Substring.dropl Char.isSpace text))

fun status_of_word word =
  case word of
      "Theorem" => SzsTheorem
    | "Unsatisfiable" => SzsTheorem
    | "CounterSatisfiable" => SzsCounterSat
    | "Satisfiable" => SzsSatisfiable
    | "GaveUp" => SzsGaveUp
    | "Unknown" => SzsGaveUp
    | "Incomplete" => SzsGaveUp
    | "Timeout" => SzsTimeout
    | "ResourceOut" => SzsResourceOut
    | "MemoryOut" => SzsResourceOut
    | "Forced" => SzsGaveUp
    | "User" => SzsGaveUp
    | "Inappropriate" => SzsInappropriate
    | other => SzsUnknown other

fun szs_name SzsTheorem = "Theorem"
  | szs_name SzsCounterSat = "CounterSatisfiable"
  | szs_name SzsSatisfiable = "Satisfiable"
  | szs_name SzsGaveUp = "GaveUp"
  | szs_name SzsTimeout = "Timeout"
  | szs_name SzsResourceOut = "ResourceOut"
  | szs_name SzsInappropriate = "Inappropriate"
  | szs_name (SzsUnknown text) = text
  | szs_name (RunFailure text) = "failure: " ^ text

fun szs_to_string (SzsUnknown text) = "Unknown:" ^ text
  | szs_to_string (RunFailure text) = "RunFailure:" ^ text
  | szs_to_string szs = szs_name szs

fun szs_of_string text =
  if String.isPrefix "Unknown:" text then
    SzsUnknown (String.extract (text, 8, NONE))
  else if String.isPrefix "RunFailure:" text then
    RunFailure (String.extract (text, 11, NONE))
  else
    case status_of_word text of
        SzsUnknown _ => raise Fail ("invalid SZS status " ^ text)
      | szs => if szs_name szs = text then szs
               else raise Fail ("invalid SZS status " ^ text)

fun szs_of_line line =
  let
    val marker = "SZS status "
    val (_, rest) = Substring.position marker (Substring.full line)
  in
    if Substring.isEmpty rest then NONE
    else
      let
        val word = first_word (Substring.triml (String.size marker) rest)
      in
        if word = "" then NONE else SOME (status_of_word word)
      end
  end

fun is_comment line =
  let val line' = Substring.dropl Char.isSpace (Substring.full line) in
    Substring.isPrefix "#" line' orelse Substring.isPrefix "%" line'
  end

fun unescape_axiom raw =
  let
    val bare = trim raw
    val unquoted =
      if String.size bare >= 2 andalso String.sub (bare, 0) = #"'" andalso
         String.sub (bare, String.size bare - 1) = #"'" then
        String.substring (bare, 1, String.size bare - 2)
      else bare
    val name = unescape unquoted handle _ => unquoted
  in
    (* Monomorphic copies replay the original theorem, so deduplication
       keeps the first occurrence of the original name. *)
    hhTptpProblem.fact_of_name name
  end

(* Scans s from start for the first character outside quotes at which
   stop (character, parenthesis depth) holds; depth starts at depth0. *)
fun scan_unquoted stop s start depth0 =
  let
    fun loop i depth quoted =
      if i = String.size s then NONE
      else
        let val c = String.sub (s, i) in
          if quoted then
            if c = #"'" then
              if i + 1 < String.size s andalso String.sub (s, i + 1) = #"'"
              then loop (i + 2) depth true
              else loop (i + 1) depth false
            else loop (i + 1) depth true
          else if c = #"'" then loop (i + 1) depth true
          else if stop (c, depth) then SOME i
          else if c = #"(" then loop (i + 1) (depth + 1) false
          else if c = #")" then loop (i + 1) (depth - 1) false
          else loop (i + 1) depth false
        end
  in
    loop start depth0 false
  end

fun comma_at_top s =
  scan_unquoted (fn (c, depth) => c = #"," andalso depth = 0) s 0 0

fun closing_paren s start =
  scan_unquoted (fn (c, depth) => c = #")" andalso depth = 1) s start 1

(* The index of the first occurrence of marker in text at or after i. *)
fun index_from marker text i =
  let
    val (_, rest) =
      Substring.position marker (Substring.extract (text, i, NONE))
  in
    if Substring.isEmpty rest then NONE else SOME (#2 (Substring.base rest))
  end

fun fold_file_names add line initial =
  let
    val marker = "file("
    fun find i names =
      case index_from marker line i of
          NONE => names
        | SOME found =>
          let
            val start = found + String.size marker
          in
            case closing_paren line start of
                NONE => names
              | SOME finish =>
                let
                  val args = String.substring (line, start, finish - start)
                  val name =
                    case comma_at_top args of
                        NONE => NONE
                      | SOME comma =>
                        unescape_axiom
                          (String.extract (args, comma + 1, NONE))
                  val names' =
                    case name of NONE => names | SOME item => add item names
                in
                  find (finish + 1) names'
                end
          end
  in
    find 0 initial
  end

fun axiom_name line =
  let
    val (_, opened) = Substring.position "(" (Substring.full line)
    (* Opening parentheses in the name and role fields are dropped. *)
    fun without_open field =
      let val text = Substring.string field in
        if String.isSubstring "(" text then
          String.translate (fn #"(" => "" | c => String.str c) text
        else text
      end
  in
    if Substring.isEmpty opened then NONE
    else
      let val (name, comma) = Substring.position "," (Substring.triml 1 opened)
      in
        if Substring.isEmpty comma then NONE
        else
          let val (role, _) = Substring.position "," (Substring.triml 1 comma)
          in
            if trim (without_open role) = "axiom" then
              unescape_axiom (without_open name)
            else NONE
          end
      end
  end

val distinct = mk_sameorder_set String.compare

fun axioms_from_tstp lines =
  let
    val empty = (Redblackset.empty String.compare, [])
    fun add name (state as (seen, names)) =
      if Redblackset.member (seen, name) then state
      else (Redblackset.add (seen, name), name :: names)
    fun collect scan = List.foldl (fn (line, state) =>
      if is_comment line then state else scan line state) empty lines
    fun from_header line state =
      case axiom_name line of
          NONE => state
        | SOME name => add name state
  in
    case #2 (collect (fold_file_names add)) of
        [] => List.rev (#2 (collect from_header))
      | names => List.rev names
  end

fun parse_tstp lines =
  case Portable.get_first szs_of_line lines of
      SOME SzsTheorem => (SzsTheorem, SOME (axioms_from_tstp lines))
    | SOME status => (status, NONE)
    | NONE => (RunFailure "no SZS status", NONE)

(* Vampire may report its own time limit without any SZS line. *)
fun parse_vampire lines =
  case parse_tstp lines of
      (RunFailure _, _) =>
        if List.exists (String.isSubstring "Time limit reached!") lines
        then (SzsTimeout, NONE)
        else (RunFailure "no SZS status", NONE)
    | result => result

fun core_axioms lines =
  let
    fun old_core line =
      case String.fields (fn c => c = #"[") line of
          _ :: tail =>
            (case String.fields (fn c => c = #"]") (String.concat tail) of
                 names :: _ =>
                   List.mapPartial unescape_axiom
                     (String.fields (fn c => c = #",") names)
               | [] => [])
        | [] => []
    val szs_marker = "% SZS core "
    fun from_line line =
      let val stripped = Substring.dropl Char.isSpace (Substring.full line) in
        if Substring.isPrefix "core" stripped then
          old_core (Substring.string stripped)
        else if Substring.isPrefix szs_marker stripped then
          List.mapPartial (unescape_axiom o Substring.string)
            (Substring.tokens Char.isSpace
              (Substring.triml (String.size szs_marker) stripped))
        else []
      end
  in
    distinct (List.concat (map from_line lines))
  end

fun parse_z3 lines =
  let
    val status =
      case Portable.get_first szs_of_line lines of
          SOME result => result
        | NONE => RunFailure "no SZS status"
  in
    case status of
        SzsTheorem => (status, SOME (core_axioms lines))
      | _ => (status, NONE)
  end

fun version_after marker text =
  case index_from marker text 0 of
      NONE => NONE
    | SOME i =>
        let
          val version =
            first_word (Substring.extract (text, i + String.size marker, NONE))
        in
          if version = "" then NONE else SOME version
        end

fun e_version output = version_after "E " output
fun vampire_version output = version_after "Vampire " output
fun zipperposition_version output = version_after "zipperposition " output

fun version_between left right text =
  case index_from left text 0 of
      NONE => NONE
    | SOME index =>
        let val start = index + String.size left in
          Option.map
            (fn finish => String.substring (text, start, finish - start))
            (index_from right text start)
        end

fun z3_version output = version_between "Z3tptp [" "]" output

fun same_slice (left : slice) right = left = right

val grace_seconds = 2

fun mk_slice prover (format, type_enc, lam_trans) filter nfacts : slice =
  {prover = prover, format = format, type_enc = type_enc,
   lam_trans = lam_trans, nfacts = nfacts, filter = filter,
   extra_opts = [], slice_size = 1}

val legacy_fof = ("fof", "", "")

(* The built-in slice portfolio, in scheduling order: the first eight
   entries are the FOF anchors, the next eight the typed and remaining
   unfiltered slices, and the final eight the filtered ensemble slices.
   Each built-in prover's slice table is its subsequence of this list. *)
val portfolio =
  [mk_slice Vampire legacy_fof "knn" 96,
   mk_slice Eprover legacy_fof "knn" 128,
   mk_slice Zipperposition legacy_fof "knn" 128,
   mk_slice Vampire legacy_fof "knn" 512,
   mk_slice Eprover legacy_fof "knn" 512,
   mk_slice Vampire legacy_fof "knn" 32,
   mk_slice Zipperposition legacy_fof "knn" 512,
   mk_slice Vampire legacy_fof "knn" 1024,

   mk_slice Vampire ("tx0", "mono_native_fool", "lifting") "knn" 96,
   mk_slice Eprover ("tx0-", "mono_native_fool", "lifting") "knn" 128,
   mk_slice Zipperposition ("th1", "mono_native_higher_fool", "keep_lams")
     "knn" 128,
   mk_slice Eprover ("th0", "mono_native_higher", "keep_lams") "knn" 512,
   (* Substitution for TF1, which Vampire 5.0.1 rejected when the
      generated TF1 bound formula type variables with !>: TH0 is the next
      tested table candidate, a parser-equivalence correction, not a
      tuning change.  The pinned build runs its generic FOF schedule on
      THF and superposes into lambda bodies with loose bound variables,
      refuting consistent axioms, so its TH0 problems are lambda-lifted. *)
   mk_slice Vampire ("th0", "mono_native_higher", "lifting") "knn" 512,
   (* Substitution: E 3.2.5-ho was recorded rejecting the TF0
      combs_and_lifting problems generated at the time; it reads and
      proves the current ones, but the slice stays TX0- (same lambda
      mode) until the portfolio is re-evaluated. *)
   mk_slice Eprover ("tx0-", "mono_native_fool", "combs_and_lifting") "knn"
     1024,
   mk_slice Vampire ("tx0", "mono_native_fool", "combs") "knn" 512,
   (* Substitution for FOF/mono_guards??: Zipperposition 2.1 rejected
      those problems with a unification error, as their guard axioms
      applied symbols to all their HOL arguments, more than the rest of
      the problem did.  Guard axioms use the problem's arities, which
      Zipperposition accepts, but the slice stays legacy FOF/32 until the
      portfolio is re-evaluated. *)
   mk_slice Zipperposition legacy_fof "knn" 32,

   mk_slice Vampire legacy_fof "mesh" 96,
   mk_slice Eprover legacy_fof "mesh" 128,
   mk_slice Zipperposition ("th1", "mono_native_higher_fool", "keep_lams")
     "mesh" 128,
   mk_slice Vampire ("tx0", "mono_native_fool", "lifting") "mesh" 512,
   mk_slice Eprover legacy_fof "mepo" 512,
   mk_slice Vampire legacy_fof "mepo" 1024,
   mk_slice Eprover ("tx0-", "mono_native_fool", "lifting") "mash" 128,
   mk_slice Vampire legacy_fof "mash" 256]

fun portfolio_slices prover =
  List.filter (fn slice => #prover slice = prover) portfolio

(* Pinned E 3.2.5-ho, Vampire 5.0.1, and Zipperposition 2.1 smoke
   recordings validate these TPTP-3 dialect choices for every typed slice.
   E's --tstp-in and Zipperposition's --input tptp are base command options;
   Vampire alone requires its explicit TPTP input selector. *)
fun e_command executable {timeout, problem, extra, ...} =
  (executable,
   ["--auto-schedule", "--tstp-in", "--tstp-out", "-s",
    "--cpu-limit=" ^ Int.toString timeout, "--proof-object=1"] @
   extra @ [problem])

fun vampire_command executable {timeout, problem, extra, ...} =
  (executable,
   ["--mode", "portfolio", "--schedule", "casc",
    "--input_syntax", "tptp",
    "--proof", "tptp", "--output_axiom_names", "on", "-t",
    Int.toString timeout] @ extra @ ["--input_file", problem])

fun zipperposition_command executable {timeout, problem, extra, ...} =
  (executable,
   ["--input", "tptp", "--output", "tptp", "--timeout",
    Int.toString timeout] @ extra @ [problem])

(* z3_tptp is Z3's TPTP front end (Z3's examples/tptp); the z3 binary
   itself reads no TPTP. *)
fun z3_command executable {timeout, problem, extra, ...} =
  (executable,
   ["-c", "-smt.pull_nested_quantifiers:true",
    "-t:" ^ Int.toString timeout] @ extra @ ["-file:" ^ problem])

val e_config : prover_config =
  {name = hhConfig.prover_name Eprover, exec_names = ["eprover-ho", "eprover"],
   env_var = "HOL4_EPROVER_EXECUTABLE", version_args = ["--version"],
   parse_version = e_version, tested_versions = ["3.2.5"],
   supported_formats = ["fof", "tf0", "tx0-", "th0"],
   mk_command = e_command,
   parse_output = parse_tstp, mono_instances = 128,
   slices = portfolio_slices Eprover, legacy = false}

val vampire_config : prover_config =
  {name = hhConfig.prover_name Vampire, exec_names = ["vampire"],
   env_var = "HOL4_VAMPIRE_EXECUTABLE", version_args = ["--version"],
   parse_version = vampire_version, tested_versions = ["5.0.1"],
   supported_formats = ["fof", "tf0", "tf1", "tx0", "th0", "th1"],
   mk_command = vampire_command,
   parse_output = parse_vampire, mono_instances = 256,
   slices = portfolio_slices Vampire, legacy = false}

val zipperposition_config : prover_config =
  {name = hhConfig.prover_name Zipperposition, exec_names = ["zipperposition"],
   env_var = "HOL4_ZIPPERPOSITION_EXECUTABLE", version_args = ["--version"],
   parse_version = zipperposition_version, tested_versions = ["2.1"],
   supported_formats = ["fof", "th1"],
   mk_command = zipperposition_command, parse_output = parse_tstp,
   mono_instances = 100,
   slices = portfolio_slices Zipperposition, legacy = false}

val z3_config : prover_config =
  {name = hhConfig.prover_name Z3, exec_names = ["z3_tptp"],
   env_var = "HOL4_Z3_TPTP_EXECUTABLE",
   version_args = ["--version"], parse_version = z3_version,
   tested_versions = ["4.11.2"], supported_formats = ["fof"],
   mk_command = z3_command,
   parse_output = parse_z3, mono_instances = 100,
   slices = [], legacy = true}

fun builtin_config Eprover = e_config
  | builtin_config Vampire = vampire_config
  | builtin_config Zipperposition = zipperposition_config
  | builtin_config Z3 = z3_config

val overrides = Portable.syncref ([] : (prover * prover_config) list)

fun config_of prover =
  case List.find (fn (other, _) => other = prover) (#get overrides ()) of
      SOME (_, config) => config
    | NONE => builtin_config prover

fun all () = map config_of hhConfig.all_provers

fun with_override prover config f =
  let
    fun set value = #upd overrides (fn _ => ((), value))
    val saved = #get overrides ()
  in
    set ((prover, config) :: saved);
    Portable.finally (fn () => set saved) f ()
  end

fun find_exec ({name, exec_names, env_var, ...} : prover_config) =
  hhConfig.find_exec name env_var exec_names

fun is_found config = Option.isSome (find_exec config)

fun default_provers () =
  List.filter (fn prover =>
    let val config = config_of prover
    in not (#legacy config) andalso is_found config end)
    hhConfig.all_provers

fun elapsed started = Time.toReal (Time.- (Time.now (), started))

fun with_mutex mutex f = Multithreading.synchronized "hhProver" mutex f

val spawns = Portable.syncref 0

fun spawn_count () = #get spawns ()

fun reset_spawn_count () = #upd spawns (fn _ => ((), 0))

fun note_spawn () = #upd spawns (fn n => ((), n + 1))

fun text_instream fd =
  let
    open Posix.IO
    val (flags, _) = getfl fd
    val reader = mkTextReader
      {fd = fd, name = "", initBlkMode = not (O.allSet (O.nonblock, flags))}
  in
    TextIO.mkInstream (TextIO.StreamIO.mkInstream (reader, ""))
  end

type process_result =
  {output : string, exec_failed : bool, killed : bool,
   status : Posix.Process.exit_status, time : real}

type process_running =
  {kill : unit -> unit,
   wait : unit -> process_result}

fun is_esrch error = OS.errorName error = "ESRCH"

(* Prover processes are started with posix_spawn(3) through the Foreign
   interface rather than with Posix.Process.fork.  Poly/ML's fork only
   marks the child single-threaded: runtime mutexes (the heap-allocation
   lock, the scheduler lock taken on every ML/RTS transition) that another
   thread holds at the time of the fork stay locked in the child, whose ML
   code between fork and exec can need them.  The child then never reaches
   exec, and the parent waits for it forever.  (Poly/ML's own Unix.execute
   was changed to fork in C for the same reason.)  posix_spawn runs only C
   code in the child, and glibc reports an exec failure as its return
   value, so no error pipe is needed. *)
local
  open Foreign
  val libc = loadExecutable ()
  (* Foreign resolves a symbol lazily, at its first call; symbolAsAddress
     forces it now, so that a missing function fails loading this module
     (with Foreign.Foreign naming it) rather than the first prover run. *)
  fun symbol name =
    let val sym = getSymbol libc name
    in ignore (symbolAsAddress sym); sym end
  val file_actions_init =
    buildCall1 (symbol "posix_spawn_file_actions_init", cPointer, cInt)
  val file_actions_dup2 = buildCall3
    (symbol "posix_spawn_file_actions_adddup2", (cPointer, cInt, cInt), cInt)
  val file_actions_destroy =
    buildCall1 (symbol "posix_spawn_file_actions_destroy", cPointer, cInt)
  val attr_init = buildCall1 (symbol "posix_spawnattr_init", cPointer, cInt)
  val attr_setflags =
    buildCall2 (symbol "posix_spawnattr_setflags", (cPointer, cShort), cInt)
  val attr_setpgroup =
    buildCall2 (symbol "posix_spawnattr_setpgroup", (cPointer, cInt), cInt)
  val attr_destroy =
    buildCall1 (symbol "posix_spawnattr_destroy", cPointer, cInt)
  val attr_setsigmask = buildCall2
    (symbol "posix_spawnattr_setsigmask", (cPointer, cPointer), cInt)
  val attr_setsigdefault = buildCall2
    (symbol "posix_spawnattr_setsigdefault", (cPointer, cPointer), cInt)
  val sigset_empty = buildCall1 (symbol "sigemptyset", cPointer, cInt)
  val sigset_full = buildCall1 (symbol "sigfillset", cPointer, cInt)
  (* The string vectors are NULL-terminated: NONE is the null pointer. *)
  val c_spawn = buildCall6
    (symbol "posix_spawn",
     (cStar cInt, cString, cPointer, cPointer,
      cVectorPointer (cOptionPtr cString),
      cVectorPointer (cOptionPtr cString)), cInt)
  (* POSIX_SPAWN_SETPGROUP, _SETSIGDEF and _SETSIGMASK have these values on
     Linux and on macOS. *)
  val spawn_setpgroup = 0x02
  val spawn_setsigdef = 0x04
  val spawn_setsigmask = 0x08
  (* The opaque posix_spawn types are smaller than this on every
     supported platform. *)
  val opaque_size = 0w1024

  (* The posix_spawn family returns an error number rather than setting
     errno. *)
  fun check name status =
    if status = 0 then ()
    else raise OS.SysErr
      (name, SOME (Posix.Error.fromWord (SysWord.fromInt status)))

  fun c_vector strs = Vector.fromList (List.map SOME strs @ [NONE])

  (* Run f on a fresh initialised opaque object, which is destroyed and
     freed when f returns or raises.  If init fails, the memory is only
     freed.  Neither this nor f may be interrupted: callers mask
     interrupts. *)
  fun with_object name (init, destroy) f =
    let
      val object = Memory.malloc opaque_size
      val _ = check name (init object) handle exn =>
        (Memory.free object; raise exn)
      fun release () = (destroy object; Memory.free object)
      val result = f object handle exn => (release (); raise exn)
    in
      release (); result
    end

  (* Run f on a sigset_t (smaller than an opaque object) set up by init;
     there is nothing to destroy. *)
  fun with_sigset name init f =
    let
      fun init_set set =
        if init set = 0 then 0 else raise OS.SysErr (name, NONE)
    in
      with_object name (init_set, fn _ => ()) f
    end

  fun fd_int fd = SysWord.toInt (Posix.FileSys.fdToWord fd)
in

(* Start path with arguments args (including argv[0]) and environment env, in
   a new process group, with the descriptor output as its stdout, and as its
   stderr too if with_stderr; otherwise it keeps the caller's stderr.  The
   child starts with an empty signal mask and every signal at its default
   disposition.  posix_spawn would otherwise pass on the calling thread's
   mask and the parent's ignored signals: Poly/ML threads block almost every
   signal, including SIGXCPU on which E's --cpu-limit relies (a runaway
   prover would go on for hours), and the runtime ignores SIGPIPE.
   NONE if the program could not be executed.  Raises OS.SysErr if the spawn
   attributes cannot be set up.  Must run with interrupts deferred: an
   interrupt between the spawn and the return of its pid would orphan the
   child. *)
fun spawn with_stderr path args env output =
  with_object "posix_spawn_file_actions_init"
    (file_actions_init, file_actions_destroy) (fn file_actions =>
  with_object "posix_spawnattr_init" (attr_init, attr_destroy) (fn attr =>
  with_sigset "sigemptyset" sigset_empty (fn no_signals =>
  with_sigset "sigfillset" sigset_full (fn all_signals =>
    let
      val dup2 = "posix_spawn_file_actions_adddup2"
      val pid = ref 0
      val _ = check "posix_spawnattr_setflags"
        (attr_setflags
           (attr, spawn_setpgroup + spawn_setsigdef + spawn_setsigmask))
      val _ = check "posix_spawnattr_setsigmask"
        (attr_setsigmask (attr, no_signals))
      val _ = check "posix_spawnattr_setsigdefault"
        (attr_setsigdefault (attr, all_signals))
      val _ = check "posix_spawnattr_setpgroup" (attr_setpgroup (attr, 0))
      val _ = check dup2 (file_actions_dup2 (file_actions, fd_int output, 1))
      val _ = if with_stderr then
                check dup2 (file_actions_dup2 (file_actions, fd_int output, 2))
              else ()
      val status = c_spawn (pid, path, file_actions, attr,
                            c_vector args, c_vector env)
    in
      if status <> 0 then NONE
      else SOME (Posix.Process.wordToPid (SysWord.fromInt (!pid)))
    end))))

end

(* pipe(2) and fcntl(2) are separate operations in the Basis interface.  Keep
   that setup window serial with the spawns so that a concurrent child does
   not inherit a pipe before its close-on-exec flags have been installed. *)
val spawn_mutex = Mutex.mutex ()

fun failed_process started : process_running =
  {kill = fn () => (),
   wait = fn () =>
     {output = "", exec_failed = true, killed = false,
      status = Posix.Process.W_EXITSTATUS 0w127, time = elapsed started}}

fun start_process with_stderr path args limit : process_running =
  let
    val started = Time.now ()
    val spawned = Thread_Attributes.uninterruptible_defer (fn _ => fn () =>
      with_mutex spawn_mutex (fn () =>
      let
        val {infd = read_fd, outfd = write_fd} = Posix.IO.pipe ()
        val close_on_exec = Posix.IO.FD.flags [Posix.IO.FD.cloexec]
        val _ = List.app (fn fd => Posix.IO.setfd (fd, close_on_exec))
          [read_fd, write_fd]
        val pid =
          spawn with_stderr path (path :: args) (Posix.ProcEnv.environ ())
            write_fd
          handle exn => (Posix.IO.close read_fd; Posix.IO.close write_fd;
                         raise exn)
        val _ = Posix.IO.close write_fd
        (* posix_spawn puts the child in its own group.  Doing it here too
           closes the race in which a caller kills immediately after
           run_async returns, on a C library (glibc before 2.24) whose
           posix_spawn returns before the child has run, and the group does
           not exist yet.  There an exec failure is also not a return value
           but the child's exit status 127, which run_async reports as
           could not execute prover; the child may be gone before setpgid. *)
        val _ = Option.app (fn pid =>
          (Posix.ProcEnv.setpgid {pid = SOME pid, pgid = SOME pid}
           handle OS.SysErr _ => ())) pid
      in
        (case pid of
             SOME _ => note_spawn ()
           | NONE => Posix.IO.close read_fd);
        Option.map (fn pid => (pid, read_fd)) pid
      end)) ()
  in
    case spawned of
        NONE => failed_process started
      | SOME (pid, read_fd) =>
      let
        val input = text_instream read_fd
        val chunks = ref ([] : string list)
        val state_mutex = Mutex.mutex ()
        val wait_mutex = Mutex.mutex ()
        val reader_done = ref false
        val process_done = ref false
        val was_killed = ref false
        val waited = ref (NONE : process_result option)
        fun state f = with_mutex state_mutex f
        fun signal_group () =
          state (fn () =>
            if !process_done orelse !was_killed then ()
            else
              let
                val signalled =
                  ((Posix.Process.kill
                      (Posix.Process.K_GROUP pid, Posix.Signal.kill);
                    true)
                   handle exn as OS.SysErr (_, SOME error) =>
                     if is_esrch error then false else raise exn)
              in
                if signalled then was_killed := true else ()
              end)
        fun read_stdout () =
          let
            fun loop () =
              case TextIO.input input of
                  "" => ()
                | chunk => (chunks := chunk :: !chunks; loop ())
          in
            (loop () handle _ => ();
             (TextIO.closeIn input handle _ => ());
             state (fn () => reader_done := true))
          end
        val _ = Thread.fork (read_stdout, [])
        fun watchdog () =
          if state (fn () => !process_done orelse !was_killed) then ()
          else if elapsed started >= limit then signal_group ()
          else
            (OS.Process.sleep (Time.fromMilliseconds 20);
             watchdog ())
        val _ = Thread.fork (watchdog, [])
        fun await_reader () =
          if state (fn () => !reader_done) then ()
          else
            (if elapsed started >= limit then signal_group () else ();
             OS.Process.sleep (Time.fromMilliseconds 20);
             await_reader ())
        fun reap () = #2 (Posix.Process.waitpid
          (Posix.Process.W_CHILD pid, []))
        fun finish () =
          let
            val _ = await_reader ()
            val status = reap ()
            val output = String.concat (List.rev (!chunks))
            val _ = chunks := []
            val result =
              {output = output, exec_failed = false,
               killed = state (fn () => !was_killed),
               status = status, time = elapsed started}
            val _ = state (fn () => process_done := true)
          in
            result
          end
        fun cleanup exn =
          let
            val attributes = Thread.getAttributes ()
            val synchronous =
              [Thread.InterruptState Thread.InterruptSynch,
               Thread.EnableBroadcastInterrupt true]
            val _ = Thread.setAttributes synchronous
            val _ = (signal_group () handle _ => ())
            val _ = (await_reader () handle _ => ())
            val _ = (ignore (reap ()) handle _ => ())
            val _ = state (fn () => process_done := true)
            val _ = Thread.setAttributes attributes
          in
            raise exn
          end
        fun wait () =
          with_mutex wait_mutex (fn () =>
            case !waited of
                SOME result => result
              | NONE =>
                  let
                    val result = finish () handle exn => cleanup exn
                    val _ = waited := SOME result
                  in
                    result
                  end)
      in
        {kill = signal_group, wait = wait}
      end
  end

fun read_process path args limit =
  #wait (start_process true path args limit) ()

fun read_stdout path args limit =
  #wait (start_process false path args limit) ()

val probes : (string *
  {path : string, version : string option, tested : bool} option) list ref =
  ref []

fun warn_untested name path version =
  TextIO.output (TextIO.stdErr,
    "HolyHammer: " ^ name ^ " at " ^ path ^ " has untested version " ^
    version ^ "\n")

fun probe (config : prover_config) =
  let
    val name = #name config
    fun unprobed path = SOME {path = path, version = NONE, tested = false}
    fun discover () =
      case find_exec config of
          NONE => NONE
        | SOME path =>
            let
              val {output, killed, ...} =
                read_process path (#version_args config) 7.0
              val version =
                if killed then NONE else (#parse_version config output)
              val tested =
                case version of
                    NONE => false
                  | SOME value => List.exists
                      (fn prefix => String.isPrefix prefix value)
                      (#tested_versions config)
              val _ =
                case version of
                    SOME value =>
                      if tested then () else warn_untested name path value
                  | NONE => warn_untested name path "unknown"
            in
              SOME {path = path, version = version, tested = tested}
            end
            handle OS.SysErr _ => unprobed path
                 | IO.Io _ => unprobed path
  in
    case List.find (fn (other, _) => other = name) (!probes) of
        SOME (_, result) => result
      | NONE =>
          let val result = discover () in
            probes := (name, result) :: !probes;
            result
          end
  end

val output_counter = Portable.make_counter {init = 1, inc = 1}

fun write_output_fd fd contents =
  let
    val bytes = Byte.stringToBytes contents
    val size = Word8Vector.length bytes
    fun write offset =
      if offset = size then ()
      else
        let
          val rest = Word8VectorSlice.slice (bytes, offset, NONE)
          val written = Posix.IO.writeVec (fd, rest)
        in
          if written = 0 then raise OS.SysErr ("empty output write", NONE)
          else write (offset + written)
        end
  in
    write 0
  end

fun save_output directory name contents =
  let
    val _ = hhConfig.ensure_dir directory
    val prefix = name ^ "-" ^ Portable.unique_tmp_suffix () ^ "-"
    (* Evaluation workers share this directory. Reserve each name
       exclusively in case a previous worker used the same process ID. *)
    fun attempt () =
      let
        val path = OS.Path.concat (directory,
          prefix ^ Int.toString (output_counter ()) ^ ".out")
        val owned = ref false
        fun open_output () =
          let
            open Posix.FileSys
            val mode = S.flags [S.irusr, S.iwusr, S.irgrp, S.iwgrp,
                                S.iroth, S.iwoth]
            val fd = createf (path, O_WRONLY, O.excl, mode)
            open Posix.IO
          in
            owned := true;
            ((setfd (fd, FD.cloexec); SOME fd)
             handle exn => (close fd; raise exn))
          end
          handle exn as OS.SysErr (_, SOME error) =>
            if not (!owned) andalso error = Posix.Error.exist
            then NONE else raise exn
        fun write NONE = NONE
          | write (SOME fd) = (write_output_fd fd contents; SOME path)
      in
        Portable.bracket (fn () => with_mutex spawn_mutex open_output)
          (Option.app Posix.IO.close) write
        handle exn =>
          (if !owned then hhConfig.remove_quietly path else (); raise exn)
      end
    fun save () = case attempt () of SOME path => path | NONE => save ()
  in
    save ()
  end

fun missing_prover ({name, env_var, ...} : prover_config) =
  "HolyHammer prover '" ^ name ^ "': " ^ hhConfig.missing_exec name env_var

fun completed result : running =
  {kill = fn () => (), wait = fn () => result}

fun run_async (config : prover_config) request =
  let
    val started = Time.now ()
    fun failure version message =
      {szs = RunFailure message, used_axioms = NONE,
       time = elapsed started, version = version, output_file = ""}
    fun could_not_execute version = failure version "could not execute prover"
  in
    case probe config of
        NONE => completed (failure NONE (missing_prover config))
      | SOME {path = executable, version, ...} =>
          ((let
              val (path, args) =
                #mk_command config executable request
              val {kill, wait = await_process} = start_process true path args
                (Real.fromInt (#timeout request + grace_seconds))
              val result_mutex = Mutex.mutex ()
              fun collect () =
                let
                  val {output, exec_failed, killed, status, time} =
                    await_process ()
                  val (parsed, used_axioms) = #parse_output config
                    (String.fields (fn c => c = #"\n") output)
                  (* A status the prover already reported is authoritative
                     even if the wall-clock guard then killed it: only fall
                     back to Timeout when nothing conclusive was parsed. *)
                  val szs =
                    case parsed of
                        RunFailure message =>
                          if exec_failed orelse
                             status = Posix.Process.W_EXITSTATUS 0w127 then
                            RunFailure "could not execute prover"
                          else if killed then SzsTimeout
                          else if status = Posix.Process.W_EXITED then
                            RunFailure message
                          else RunFailure "prover exited unsuccessfully"
                      | value => value
                  val output_file =
                    case #debug_dir request of
                        NONE => ""
                      | SOME directory =>
                          save_output directory (#name config) output
                in
                  {szs = szs, used_axioms = used_axioms, time = time,
                   version = version, output_file = output_file}
                end
              (* Release the raw output held by await_process once it has
                 been parsed. Repeated waits need only the parsed result. *)
              val saved = Susp.delay (fn () =>
                collect ()
                handle OS.SysErr _ => could_not_execute version
                     | IO.Io _ => could_not_execute version)
              fun wait () =
                with_mutex result_mutex (fn () => Susp.force saved)
            in
              {kill = kill, wait = wait}
           end)
           handle OS.SysErr _ => completed (could_not_execute version)
                | IO.Io _ => completed (could_not_execute version))
  end

fun run config request = #wait (run_async config request) ()

end
