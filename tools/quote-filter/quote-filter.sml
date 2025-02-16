open OS.Process qfilter_util

(* magic to ensure that interruptions (SIGINTs) are actually seen by the
   linked executable as Interrupt exceptions *)
prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

val {instrm = instream, outstrm = outstream, interactive = intp,
     quotefixp = qfixp, closefn = callback, infilename} =
    processArgs (false,false,false) (CommandLine.arguments())

(* with many thanks to Ken Friis Larsen, Peter Sestoft, Claudio Russo and
   Kenn Heinrich who helped me see the light with respect to this code *)
fun read _ = TextIO.input instream
fun write s = TextIO.output (outstrm, s)

val _ = if quotefixp then
  quotefix.run read write
else let
  open HolParser.ToSML
  val read = mkPushTranslator {
    read = read,
    filename = infilename,
    parseError = fn (start, stop) => fn s =>
      TextIO.output (TextIO.stdErr,
        "parse error at " ^ Int.toString start ^ "-" ^ Int.toString stop ^ ": " ^ s ^ "\n")
  } (mkStrcode write)

  fun loop () = if read () then () else loop ()
  in loop () end

val _ = callback()
val _ = exit success
