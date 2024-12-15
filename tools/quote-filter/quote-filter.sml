open OS.Process qfilter_util

(* magic to ensure that interruptions (SIGINTs) are actually seen by the
   linked executable as Interrupt exceptions *)
prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

fun read_from_stream is n = TextIO.input is

val {instrm = instream, outstrm = outstream, interactive = intp,
     quotefixp = qfixp, oldparser = oldp, closefn = callback, infilename} =
    processArgs (false,false,false,false) (CommandLine.arguments())

(* with many thanks to Ken Friis Larsen, Peter Sestoft, Claudio Russo and
   Kenn Heinrich who helped me see the light with respect to this code *)
val loop =
  if oldp orelse qfixp then let
    open QuoteFilter.UserDeclarations
    val state as QFS args = newstate {inscriptp = intp, quotefixp = qfixp,
                                      scriptfilename = infilename}

    fun loop() =
      let
        val lexer = #2 o QuoteFilter.makeLexer (read_from_stream instream) state
        fun coreloop () =
          case lexer() of
              "" => ()
            | s => (TextIO.output(outstream, s); coreloop())
      in
        coreloop() handle Interrupt => (resetstate state; loop())
      end
    in loop end
  else let
    open HolParser.ToSML
    val read = mkPushTranslator {
      read = read_from_stream instream,
      filename = infilename,
      parseError = fn (start, stop) => fn s =>
        TextIO.output (TextIO.stdErr,
          "parse error at " ^ Int.toString start ^ "-" ^ Int.toString stop ^ ": " ^ s ^ "\n")
    } (mkStrcode (fn s => TextIO.output(outstream, s)))

    fun loop () = if read () then () else loop ()
    in loop end

val _ = loop()
val _ = callback()
val _ = exit success
