signature HOL_REPL =
sig
  val sigint_handler : unit -> unit
  val topLevel : (string -> unit) ->
                 {nameSpace : PolyML.NameSpace.nameSpace,
                  exitLoop : unit -> bool, startExec : unit -> unit,
                  endExec : unit -> unit, exitOnError : bool,
                  isInteractive : bool,
                  zeroTerm : bool} -> unit
end;


structure HOL_REPL :> HOL_REPL =
struct

fun printOut s =
  (TextIO.output(TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut)
val prompt1 = PolyML.Compiler.prompt1
val prompt2 = PolyML.Compiler.prompt2
val timing = PolyML.Compiler.timing

(* code here derived from Poly/ML's implementation of its REPL.  Poly/ML code
   is all under LGPL; see required copy at doc/copyrights/lgpl2.1.txt
*)
fun topLevel diag {nameSpace, exitLoop, exitOnError, isInteractive, zeroTerm,
                   startExec, endExec} =
  let
    (* This is used as the main read-eval-print loop.  It is also invoked
       by running code that has been compiled with the debug option on
       when it stops at a breakpoint.  In that case debugEnv contains an
       environment formed from the local variables.  This is placed in front
       of the normal top-level environment. *)

    (* Don't use the end_of_stream because it may have been set by typing
       EOT to the command we were running. *)
    val endOfFile    = ref false;

    fun reportTiming compileTime runTime =
      (* Print the times if required. *)
      if !timing
      then printOut(concat["Timing - compile: ", Time.fmt 1 compileTime,
        " run: ", Time.fmt 1 runTime, "\n"])
      else ()

    fun reportResult NONE = () (* No exceptions raised. *)
      | reportResult (SOME exn) = (* Report exceptions in running code. *)
        let
          open PolyML PolyML.Exception PolyML.Compiler
          val exLoc =
            case exceptionLocation exn of
              NONE => []
            | SOME loc => [ContextLocation loc]
        in
          PolyML.prettyPrint(TextIO.print, !lineLength)
            (PrettyBlock(0, false, [], [
              PrettyBlock(0, false, exLoc,
                [PrettyString "Exception-"]),
              PrettyBreak(1, 3),
              prettyRepresentation(exn,
                FixedInt.fromInt (! printDepth)),
              PrettyBreak(1, 3),
              PrettyString "raised"
            ]));
          PolyML.Exception.reraise exn
        end

    val polyCompiler = PolyML.compiler
    fun readEvalPrint1 readin resetAfterCompileFail :
        {compileTime : Time.time, runTime : Time.time, result : exn option} =
      let
        (* If we have executed a deeply recursive function the stack
           will have extended to be very large. It's better to reduce
           the stack if we can. This is RISKY. Each function checks on
           entry that the stack has sufficient space for everything it
           will allocate and assumes the stack will not shrink. It's
           unlikely that any of the functions here will have asked for
           very much but as a precaution we allow for an extra 8k
           words. *)
        (*
        fun shrink_stack (newsize : int) : unit =
          RunCall.run_call1 RuntimeCalls.POLY_SYS_shrink_stack newsize
        val () = shrink_stack 8000 *)
        val _ = diag "At top of readEvalPrint"

        (* Compile and then run the code. *)
        val startCompile = Timer.startCPUTimer()

        (* Compile a top-level declaration/expression. *)
        val code = let
          open PolyML.Compiler
        in
          polyCompiler (readin, [CPNameSpace nameSpace,
                                 CPOutStream TextIO.print])
        end
            (* Don't print any times if this raises an exception. *)
            handle exn as Fail s => (
              printOut(s ^ "\n");
              resetAfterCompileFail();
              PolyML.Exception.reraise exn
            )

        val endCompile = Timer.checkCPUTimer startCompile

        (* Run the code *)
        val startRun = Timer.startCPUTimer()
        val () = startExec() (* Enable any debugging *)
        (* Run the code and capture any exception (temporarily). *)
        val finalResult = (code(); NONE) handle exn => SOME exn
        val () = endExec() (* Turn off debugging *)
        val endRun = Timer.checkCPUTimer startRun
      in
        {compileTime = #usr endCompile + #sys endCompile,
         runTime = #usr endRun + #sys endRun,
         result = finalResult}
      end; (* readEvalPrint1 *)

    val readEvalPrint : unit -> unit =
      if zeroTerm then
        let
          (* Initial prompt / end of splash message *)
          val () = printOut "\000";

          (* The input state is one of:
             * `Current ""`: initial state, we have no pending input chunk
             * `Current chunk`: we have a pending input chunk in the
               current command
             * `Next chunk`: The input to the current command is exhausted,
               and `chunk` is pending input for the next command *)
          datatype state =
            Current of string
          | Next of string
          val state = ref (Current "");

          (* Parse a pending input chunk, splitting on the first zero byte *)
          fun process chunk =
            let fun findZero i =
              if i < String.size chunk then
                if String.sub(chunk,i) = #"\000" then
                 (state := Next (String.extract(chunk,i+1,NONE));
                  String.substring(chunk,0,i))
                else findZero (i+1)
              else (state := Current ""; chunk)
            in findZero 0 end

          (* This is the input function we give to the lexer. It filters `stdIn`
             to ensure that we do not yield any data to it which is not for
             this command, and also avoid data loss if it asks for more from
             the stream. *)
          fun input _ =
            case !state of
              Next _ => ""
            | Current "" => (case TextIO.input TextIO.stdIn of
                "" => (endOfFile := true; "")
              | chunk => process chunk)
            | Current chunk => process chunk

          (* Moves to the next state if another statement is ready. *)
          fun finishCommand () =
            case !state of
              Next s => state := Current s
            | _ => () (* this can only happen if endOfFile is true *)

        in fn () =>
          let
            (* Create a new lexer for each command block. *)
            val {read, ...} = HolParser.inputToReader true "" input;
            val endOfBlock = ref false;
            fun read' () = case read () of
                NONE => (endOfBlock := true; NONE)
              | ch => ch;

            fun readEvalPrint compileAcc runAcc =
              let
                val {compileTime, runTime, result} =
                  readEvalPrint1 read' (fn () => ());
                val () = reportResult result;
              in
                if !endOfBlock then
                  (finishCommand (); reportTiming compileTime runTime)
                else
                  readEvalPrint (compileAcc + compileTime) (runAcc + runTime)
              end;
          in readEvalPrint Time.zeroTime Time.zeroTime end
        end
      else (* not zeroTerm *)
        let
          val realDataRead = ref false;
          val lastWasEol   = ref true;

          (* It seems like the only way to *really* reset a lexer, in particular, to
            force it back into its INITIAL state, is to create a fresh one. So,
            this is what bind_cgen() does, and this is what is called in the
            compile-fail exception handler below. *)
          val cgenref = ref (fn () => SOME #"\000")
          fun cgen() = !cgenref()
          fun bind_cgen () =
              let
                val {read, ...} = HolParser.streamToReader true "" TextIO.stdIn
              in
                cgenref := read
              end

          val () = bind_cgen();

          (* Each character typed is fed into the compiler but leading
            blank lines result in the prompt remaining as firstPrompt until
            significant characters are typed. *)
          fun readin () =
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
              | SOME #"\n" => (lastWasEol := true; SOME #"\n")
              | SOME ch => (
                  lastWasEol := false;
                  if ch <> #" " then realDataRead := true else ();
                  SOME ch
                )
            end; (* readin *)

          (* Remove all buffered but unread input. *)
          fun flushInput () =
            case TextIO.canInput(TextIO.stdIn, 1) of
                SOME 1 => (TextIO.inputN(TextIO.stdIn, 1); flushInput())
            |   _ => (* No input waiting or we're at EOF. *) ();

          fun resetAfterCompileFail () = (
            flushInput();
            lastWasEol := true;
            bind_cgen()
          );

        in fn () =>
          let
            (* If we have executed a deeply recursive function the stack
              will have extended to be very large. It's better to reduce
              the stack if we can. This is RISKY. Each function checks on
              entry that the stack has sufficient space for everything it
              will allocate and assumes the stack will not shrink. It's
              unlikely that any of the functions here will have asked for
              very much but as a precaution we allow for an extra 8k
              words. *)
            (*
            fun shrink_stack (newsize : int) : unit =
              RunCall.run_call1 RuntimeCalls.POLY_SYS_shrink_stack newsize
            val () = shrink_stack 8000 *)
            val _ = realDataRead := false
            val {compileTime, runTime, result} =
              readEvalPrint1 readin resetAfterCompileFail
            val () = reportTiming compileTime runTime
          in reportResult result end
        end; (* readEvalPrint *)

    fun handledLoop () : unit =
      (
        (* Process a single top-level command. *)
        readEvalPrint()
        handle Thread.Thread.Interrupt =>
          (* Allow ^C to terminate the debugger and raise Interrupt in
            the called program. *)
          if exitOnError then OS.Process.exit OS.Process.failure else ()
        | _ =>
          if exitOnError then OS.Process.exit OS.Process.failure else ();
        if zeroTerm then printOut "\000" else ();
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

end (* struct *)
