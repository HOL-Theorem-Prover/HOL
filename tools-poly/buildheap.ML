val _ = use "poly/poly-init2.ML";
structure BasicIO = SML90;
exception Interrupt = SML90.Interrupt

val _ = use "../tools/Holmake/Systeml.sig"
val _ = use "Holmake/Systeml.sml";

val _ = use "../tools/Holmake/hmcore.ML";
val _ = use "../tools/Holmake/GetOpt.sig";
val _ = use "../tools/Holmake/GetOpt.sml";
val _ = use "../tools/Holmake/FunctionalRecordUpdate.sml";

val SIGOBJ = OS.Path.concat(Systeml.HOLDIR, "sigobj")
datatype option_record = OR of {
  all_forced : bool,
  base_state : string option,
  debug : bool,
  forced_objs : string list,
  help : bool,
  output : string option,
  quietp : bool,
  repl : bool
}

local
  open FunctionalRecordUpdate
  fun makeUpdateT z = makeUpdate8 z
in
fun updateT z = let
  fun from all_forced base_state debug forced_objs help output quietp repl =
    {all_forced = all_forced, base_state = base_state, debug = debug,
     forced_objs = forced_objs, help = help, output = output, quietp = quietp,
     repl = repl}
  fun from' repl quietp output help forced_objs debug base_state all_forced =
    {all_forced = all_forced, base_state = base_state, debug = debug,
     forced_objs = forced_objs, help = help, output = output, quietp = quietp,
     repl = repl}
  fun to f {all_forced, base_state, debug, forced_objs, help, output, quietp,
            repl} =
    f all_forced base_state debug forced_objs help output quietp repl
in
  makeUpdateT (from, from', to)
end z
val U = U
val $$ = $$
end (* FRU local *)

local
open TextIO
in
fun warn s = (output(stdErr, s ^ "\n"); flushOut stdErr)
fun die (s:string) : 'a = (warn s; OS.Process.exit OS.Process.failure)
end

fun mk_quiet (OR r) = OR (updateT r (U #quietp true) $$);

local
  open GetOpt
 fun mkBoolT sel = NoArg (fn () => fn (OR r) => OR (updateT r (U sel true) $$))
 fun setStringOpt argnm sel =
   ReqArg ((fn s => fn (OR r) => OR (updateT r (U sel (SOME s)) $$)), argnm)
 val setBaseNone =
     NoArg (fn () => fn (OR r) => OR (updateT r (U #base_state NONE) $$))
 val ConsForced =
   ReqArg ((fn s => fn (OR r) =>
               OR (updateT r (U #forced_objs (#forced_objs r @ [s])) $$)),
           "file.uo")
in
val cline_opts = [
  {help = "provide debug output", long = ["dbg"], short = "",
   desc = mkBoolT #debug},
  {help = "force all object files", long = [], short = "F",
   desc = mkBoolT #all_forced},
  {help = "force file (will load before others)", long = [], short = "f",
   desc = ConsForced},
  {help = "show this message", long = ["help"], short = "h?",
   desc = mkBoolT #help},
  {help = "load holstate as base", long = ["holstate"], short = "b",
   desc = setStringOpt "filename" #base_state},
  {help = "output heap name", long = [], short = "o",
   desc = setStringOpt "filename" #output},
  {help = "use poly as base", long = ["poly"], short = "",
   desc = setBaseNone},
  {help = "reduce verbosity", long = ["quiet"], short = "q",
   desc = mkBoolT #quietp},
  {help = "start REPL after loading", long = ["repl"], short = "",
   desc = mkBoolT #repl}
]
val heapname = ref (SOME Systeml.DEFAULT_STATE)
val initial_cline = OR {all_forced = false,
                        base_state = !heapname,
                        debug = false,
                        forced_objs = [],
                        help = false,
                        output = NONE,
                        quietp = false,
                        repl = false}
end

fun member s [] = false
  | member s (h::t) = s = h orelse member s t

fun fullPath ps = List.foldl (fn (p,acc) => OS.Path.concat(acc,p))
                             (hd ps) (tl ps);


fun mkAbs p = OS.Path.mkAbsolute {relativeTo = OS.FileSys.getDir(), path = p}

fun findUo [] _ = NONE
  | findUo (search::rest) modPath =
      let val path =
         OS.Path.mkAbsolute
           {path = modPath, relativeTo = OS.Path.mkAbsolute
                                           {path=search,
                                            relativeTo = OS.FileSys.getDir ()}};
      in
        if OS.FileSys.access (path, []) then
          SOME path
        else
          findUo rest modPath
      end;

fun check_objpath die incs (p, b) =
  if b then ()
  else
    if member (OS.Path.dir p) (SIGOBJ::incs) then ()
    else die ("Object file "^p^" has suspicious path; use -f to override")

fun time_max (t1, t2) = if Time.<(t1,t2) then t2 else t1

fun create_heap qp findMod (objs, outputheap) = let
  open Systeml TextIO
  val p = if qp then fn s => () else fn s => print (s ^ "\n")
  fun hload obj = (p ("Loading "^obj); load obj)
                  handle e => die ("Loading "^obj^": "^General.exnMessage e)
in
  app hload objs;
  PolyML.SaveState.saveChild
    (outputheap, length (PolyML.SaveState.showHierarchy()));
  p ("Exported "^outputheap^"\n");
  (case OS.Process.getEnv Systeml.build_after_reloc_envvar of
      NONE => ()
    | SOME "1" =>
      let
        val getTime = OS.FileSys.modTime o findMod
        fun foldthis (modname, t0) = time_max(t0, getTime modname)
      in
        OS.FileSys.setTime
          (outputheap, SOME (foldl foldthis Time.zeroTime objs))
      end
    | SOME s =>
      warn ("Ignoring strange value (" ^ s ^ ") for " ^
            Systeml.build_after_reloc_envvar));
  OS.Process.exit OS.Process.success
end

fun maybe_check_load (obj,_) =
  let
    open OS.Path
    val {base,ext} = splitBaseExt obj
  in
    case ext of
        SOME "sml" => QUse.use obj
      | SOME "ML" => QUse.use obj
      | NONE => load obj
      | _ => die ("Not sure what to do with 'object file': "^obj)
  end

fun fix s =
  let
    open OS.Path
    val {base,ext} = splitBaseExt s
  in
    case ext of
        SOME "uo" => base
      | _ => s
  end

fun printOut s =
  (TextIO.output(TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut)
val prompt1 = PolyML.Compiler.prompt1
val prompt2 = PolyML.Compiler.prompt2
val timing = PolyML.Compiler.timing
fun topLevel diag {nameSpace, exitLoop, exitOnError, isInteractive, startExec,
                   endExec} =
  let
    (* This is used as the main read-eval-print loop.  It is also invoked
       by running code that has been compiled with the debug option on
       when it stops at a breakpoint.  In that case debugEnv contains an
       environment formed from the local variables.  This is placed in front
       of the normal top-level environment. *)

    (* Don't use the end_of_stream because it may have been set by typing
       EOT to the command we were running. *)
    val endOfFile    = ref false;
    val realDataRead = ref false;
    val lastWasEol   = ref true;
    val cgen = QFRead.streamToReader true TextIO.stdIn

    (* Each character typed is fed into the compiler but leading
       blank lines result in the prompt remaining as firstPrompt until
       significant characters are typed. *)
    fun readin cgen () : char option =
      let
        val () =
            if isInteractive andalso !lastWasEol (* Start of line *) then
              if !realDataRead then
                printOut (!prompt2)
              else printOut (!prompt1)
            else ();
      in
        case cgen() of
            NONE => (endOfFile := true; NONE)
         |   SOME #"\n" => ( lastWasEol := true; SOME #"\n" )
         |   SOME ch =>
             (
               lastWasEol := false;
               if ch <> #" " then realDataRead := true else ();
               SOME ch
             )
      end; (* readin *)

    (* Remove all buffered but unread input. *)
    fun flushInput () =
      case TextIO.canInput(TextIO.stdIn, 1) of
          SOME 1 => (TextIO.inputN(TextIO.stdIn, 1); flushInput())
       |   _ => (* No input waiting or we're at EOF. *) ()

    val polyCompiler = PolyML.compiler
    fun readEvalPrint () : unit =
      let
        (* If we have executed a deeply recursive function the stack
           will have extended to be very large. It's better to reduce
           the stack if we can. This is RISKY. Each function checks on
           entry that the stack has sufficient space for everything it
           will allocate and assumes the stack will not shrink. It's
           unlikely that any of the functions here will have asked for
           very much but as a precaution we allow for an extra 8k
           words. *)

        fun shrink_stack (newsize : int) : unit =
          RunCall.run_call1 RuntimeCalls.POLY_SYS_shrink_stack newsize
        val () = shrink_stack 8000
        val _ = diag "At top of readEvalPrint"
      in
        realDataRead := false;
                (* Compile and then run the code. *)
        let
          val startCompile = Timer.startCPUTimer()

          (* Compile a top-level declaration/expression. *)
          val code = let
            open PolyML.Compiler
          in
            polyCompiler (readin cgen , [CPNameSpace nameSpace,
                                         CPOutStream TextIO.print])
          end
              (* Don't print any times if this raises an exception. *)
              handle exn as Fail s =>
                        (
                            printOut(s ^ "\n");
                            flushInput();
                            lastWasEol := true;
                            PolyML.Exception.reraise exn
                        )

          val endCompile = Timer.checkCPUTimer startCompile

          (* Run the code *)
          val startRun = Timer.startCPUTimer()
          val () = startExec() (* Enable any debugging *)
          (* Run the code and capture any exception (temporarily). *)
          val finalResult = (code(); NONE) handle exn => SOME exn
          val () = endExec() (* Turn off debugging *)
          (* Print the times if required. *)
          val endRun = Timer.checkCPUTimer startRun
          val () =
              if !timing
              then printOut(
                  concat["Timing - compile: ",
                         Time.fmt 1 (#usr endCompile + #sys endCompile),
                         " run: ", Time.fmt 1 (#usr endRun + #sys endRun), "\n"]
                 )
              else ()
        in
          case finalResult of
              NONE => () (* No exceptions raised. *)
           |   SOME exn => (* Report exceptions in running code. *)
               let
                 open PolyML PolyML.Exception PolyML.Compiler
                 val exLoc =
                     case exceptionLocation exn of
                         NONE => []
                      |   SOME loc => [ContextLocation loc]
               in
                 PolyML.prettyPrint(TextIO.print, !lineLength)
                   (PrettyBlock(0, false, [],
                                [
                                  PrettyBlock(0, false, exLoc,
                                              [PrettyString "Exception-"]),
                                  PrettyBreak(1, 3),
                                  prettyRepresentation(exn, ! printDepth),
                                  PrettyBreak(1, 3),
                                  PrettyString "raised"
                   ]));
                 PolyML.Exception.reraise exn
               end
        end
      end; (* readEvalPrint *)

    fun handledLoop () : unit =
      (
        (* Process a single top-level command. *)
        readEvalPrint()
        handle Thread.Thread.Interrupt =>
               (* Allow ^C to terminate the debugger and raise Interrupt in
                  the called program. *)
               if exitOnError then OS.Process.exit OS.Process.failure
               else ()
           |   _ =>
               if exitOnError then OS.Process.exit OS.Process.failure else ();
                (* Exit if we've seen end-of-file or we're in the debugger
                   and we've run "continue". *)
        if !endOfFile orelse exitLoop() then ()
        else handledLoop ()
      )
  in
    handledLoop ()
  end

(* Set up a handler for SIGINT if that is currently set to SIG_DFL.
   If a handler has been set up by an initialisation function don't
   replace it. *)
fun sigint_handler() =
  let
    open Signal
  in
    case signal(2, SIG_IGN) of
        SIG_IGN => ()
     |  SIG_DFL =>
        (signal(2, SIG_HANDLE (fn _ => Thread.Thread.broadcastInterrupt())); ())
     |  oldHandle => (signal(2, oldHandle); ())
  end;


fun main() = let
  val usage_header =
    "Usage:\n  " ^ CommandLine.name() ^ " [options] obj1.uo obj2.uo ...\n\n\
    \Object files can be provided with .uo suffixes or not. If they are not\n\
    \present, they will be assumed. \"Object\" files may also be .sml/.ML\n\
    \files which will be used directly (without any dependency analysis being\n\
    \done).\n\n\
    \If a -o option is provided, a heap containing the context generated\n\
    \by loading/executing the .uo files will be dumped. Otherwise, the files\n\
    \are loaded solely for their side effects.\n\n\
    \If a --holstate option is not given, the operation will be with respect\n\
    \to the core HOL state that contains bossLib, lists and sets.\n\n\
    \Forcing a file means that it will be loaded even though it is in a\n\
    \directory not included in the current directory's Holmakefile's INCLUDES\n\
    \specifications.\n\n\
    \Options:"
  val usage =
      GetOpt.usageInfo {header = usage_header,
                        options = cline_opts}
  val (cline_upds, objs0) =
      GetOpt.getOpt {argOrder = GetOpt.Permute, options = cline_opts,
                     errFn = die}
                    (CommandLine.arguments())
  val OR options = List.foldl (fn (f, opts) => f opts) initial_cline cline_upds
  val {quietp = qp, output, base_state, all_forced, forced_objs, ...} = options
  val {repl, help, debug, ...} = options
  val diag = if debug then (fn s => warn ("DIAG: "^s)) else (fn s => ())
  val _ = not help orelse (print usage; OS.Process.exit OS.Process.success)
  val _ =
      case (repl, output) of
          (true, SOME _) =>
            die "Can't simultaneously dump output and start REPL"
        | _ => ()
  fun force s = (fix s, true)
  fun unforce s = (fix s, false)
  val forced_objs = map force forced_objs
  val objs = if all_forced then forced_objs @ map force objs0
             else forced_objs @ map unforce objs0
  val _ = diag ("#objs = "^Int.toString (length objs))
  val warn = if qp then (fn s => ()) else warn
  val original_die = die
  fun die s = if qp then OS.Process.exit OS.Process.failure else original_die s
  val allincs =
      if OS.FileSys.access ("Holmakefile", [OS.FileSys.A_READ]) then let
        open Holmake_types
        val (env, _, _) = ReadHMF.read "Holmakefile" (base_environment())
        fun envlist id =
          map dequote (tokenize (perform_substitution env [VREF id]))
      in
        envlist "INCLUDES" @ envlist "PRE_INCLUDES"
      end handle e =>
                 (warn "[bogus Holmakefile in current directory - ignoring it]";
                  [])
      else []
  val _ = diag ("allincs = ["^String.concatWith ", " allincs ^"]")
  val _ = case base_state of
              NONE => (diag "Not loading a base state"; heapname := NONE)
            | SOME f => (diag ("About to load base-state "^f);
                         heapname := SOME f;
                         PolyML.SaveState.loadState f)
in
  case output of
      SOME s =>
      let
        val _ = List.app (check_objpath die ("" :: "." :: allincs)) objs
        val search_these =
            "." :: OS.Path.concat(Systeml.HOLDIR, "sigobj") :: allincs
        fun findmod s =
          case findUo search_these (s ^ ".uo") of
              NONE => die ("In "^OS.FileSys.getDir()^": couldn't find "^s^
                           ".uo\n\
                           \After searching: " ^
                           String.concatWith ", " search_these)
            | SOME p => p
      in
        heapname := SOME s;
        create_heap qp findmod (map #1 objs, s)
      end
    | NONE =>
      (List.app maybe_check_load objs;
       if repl then
         (diag "Starting REPL";
          PolyML.print_depth 100;
          sigint_handler();
          topLevel diag {startExec = fn () => (),
                         endExec = fn () => (),
                         exitLoop = fn () => false,
                         exitOnError = false,
                         isInteractive = true,
                         nameSpace = PolyML.globalNameSpace} )
       else ();
       OS.Process.exit OS.Process.success)
end handle e => die ("Uncaught exception: "^General.exnMessage e)
