signature REFUTE_FORL_SAT = sig
  val configured_sat_solvers : bool -> string list
  val smart_sat_solver_name : bool -> string
  val executable_available : string -> bool
  val sat_solver_spec : Time.time -> string -> string * string list
end

structure Refute_ForlSat :> REFUTE_FORL_SAT = struct
  datatype sink = ToStdout | ToFile
  datatype availability = Java | JNI of string
  datatype mode = Batch | Incremental

  datatype sat_solver_info =
    Internal of availability * mode * string list
  | External of string * string * string list
  | ExternalV2 of
      sink * string * string * string * string * string *
      (Time.time -> string list)

  (* Environment, platform and file probes are shared with Refute_Forl,
     which loads first; the JNI directory in particular must stay the very
     same computation as the one baked into the launcher command. *)
  val getenv = Refute_Forl.getenv
  val uname = Refute_Forl.uname

  fun to_seconds minimum time =
    Int.max
      (minimum,
       LargeInt.toInt ((Time.toMilliseconds time + 999) div 1000))

  val berkmin_executable = getenv "BERKMIN_EXE"

  val static_list =
    [("CryptoMiniSat",
      External ("CRYPTOMINISAT_HOME", "cryptominisat", [])),
     ("MiniSat",
      ExternalV2
        (ToFile, "MINISAT_HOME", "minisat", "SAT", "", "UNSAT",
         fn timeout =>
           ["-cpu-lim=" ^ Int.toString (to_seconds 1 timeout)])),
     ("zChaff",
      ExternalV2
        (ToStdout, "ZCHAFF_HOME", "zchaff", "Instance Satisfiable", "",
         "Instance Unsatisfiable", fn _ => [])),
     ("RSat",
      ExternalV2
        (ToStdout, "RSAT_HOME", "rsat", "s SATISFIABLE", "v ",
         "s UNSATISFIABLE", fn _ => ["-s"])),
     ("Riss3g", External ("RISS3G_HOME", "riss3g", [])),
     ("BerkMin",
      ExternalV2
        (ToStdout, "BERKMIN_HOME",
         if berkmin_executable = "" then "BerkMin561"
         else berkmin_executable,
         "Satisfiable          !!", "solution =",
         "UNSATISFIABLE          !!", fn _ => [])),
     ("BerkMin_Alloy",
      External ("BERKMINALLOY_HOME", "berkmin", [])),
     ("SAT4J", Internal (Java, Incremental, ["DefaultSAT4J"])),
     ("SAT4J_Light", Internal (Java, Incremental, ["LightSAT4J"])),
     ("Lingeling_JNI",
      Internal (JNI "liblingeling", Batch, ["Lingeling"])),
     ("CryptoMiniSat_JNI",
      Internal (JNI "libcryptominisat", Batch, ["CryptoMiniSat"])),
     ("MiniSat_JNI",
      Internal (JNI "libminisat", Incremental, ["MiniSat"]))]

  fun library_suffix () =
    if uname "sysname" = "Darwin" then ".dylib" else ".so"

  fun jni_library_exists stem =
    getenv "HOL4_KODKODI" <> "" andalso
    Refute_Forl.readable_file
      (OS.Path.concat (Refute_Forl.jni_dir (), stem ^ library_suffix ()))

  fun external_executable (home, executable) =
    OS.Path.concat
      (getenv home,
       if Systeml.OS = "winNT" then executable ^ ".exe" else executable)

  fun executable_available path =
    OS.FileSys.access
      (path, [OS.FileSys.A_READ, OS.FileSys.A_EXEC])
    handle OS.SysErr _ => false

  fun external_entry name device home executable arguments markers =
    if getenv home = "" orelse
       not (executable_available (external_executable (home, executable)))
    then NONE
    else
      let
        fun make_arguments () =
          let
            (* Kodkodi is given this path for the solver's CNF file: the
               External solvers write it there and never delete it, so a
               solve must, while ExternalV2 ignores it and cleans up after
               itself.  An absolute scratch path keeps it out of the
               caller's directory, which the launcher does not change. *)
            val input = Refute_Forl.scratch_file_path "cnf"
          in
            [if null markers then "External" else "ExternalV2",
             external_executable (home, executable), input] @
            (if null markers then []
             else [if device = ToFile then "out" else ""]) @
            markers @ arguments
          end
      in
        SOME (name, make_arguments)
      end

  fun dynamic_entry _ incremental
      (name, Internal (Java, mode, solver)) =
        if incremental andalso mode = Batch then NONE
        else SOME (name, fn () => solver)
    | dynamic_entry _ incremental
        (name, Internal (JNI library, mode, solver)) =
        if not Systeml.isUnix orelse
           (incremental andalso mode = Batch) orelse
           not (jni_library_exists library)
        then NONE
        else SOME (name, fn () => solver)
    | dynamic_entry _ true (_, External _) = NONE
    | dynamic_entry timeout false
        (name, External (home, executable, arguments)) =
        external_entry name ToStdout home executable arguments []
    | dynamic_entry _ true (_, ExternalV2 _) = NONE
    | dynamic_entry timeout false
        (name, ExternalV2
          (device, home, executable, sat, instance, unsat, arguments)) =
        external_entry name device home executable (arguments timeout)
          [sat, instance, unsat]

  fun dynamic_list timeout incremental =
    let
      val configured =
        List.mapPartial (dynamic_entry timeout incremental) static_list
      fun java_solver (name, _) =
        name = "SAT4J" orelse name = "SAT4J_Light"
    in
      if incremental then configured
      else
        (* Prefer a configured native or external solver to the always
           available Java fallbacks, unlike Nitpick's smart selection,
           which takes the first configured entry in table order and so
           never picks a JNI solver by itself.  This puts the first
           available JNI solver (Lingeling on the x86_64 components,
           MiniSat where that is the only library shipped) ahead of SAT4J,
           while incremental smart selection still starts with SAT4J. *)
        List.filter (not o java_solver) configured @
        List.filter java_solver configured
    end

  fun configured_sat_solvers incremental =
    List.map #1 (dynamic_list Time.zeroTime incremental)

  fun smart_sat_solver_name incremental =
    case dynamic_list Time.zeroTime incremental of
        [] => "SAT4J"
      | entry :: _ => #1 entry

  fun solver_names entries =
    String.concatWith ", " (List.map (Portable.quote o #1) entries)

  fun fail function message =
    raise Feedback.mk_HOL_ERR "Refute_ForlSat" function message

  fun sat_solver_spec timeout name =
    case List.find (fn (candidate, _) => candidate = name)
        (dynamic_list timeout false) of
        SOME (_, arguments) => (name, arguments ())
      | NONE =>
          if List.exists (fn (candidate, _) => candidate = name) static_list
          then fail "sat_solver_spec"
            ("The SAT solver " ^ Portable.quote name ^
             " is not configured. The following solvers are configured:\n" ^
             solver_names (dynamic_list timeout false))
          else fail "sat_solver_spec"
            ("Unknown SAT solver " ^ Portable.quote name ^
             "\nThe following solvers are supported:\n" ^
             solver_names static_list)
end
