(* build command line tool *)
use "header.sml";
use "holfoot_command_line.sml";

fun read_from_stream is n = TextIO.input is

fun unquote_to ifile ofile =
let
     val is = TextIO.openIn ifile
     val os = TextIO.openOut ofile

     open filter.UserDeclarations
     val state as QFS args =
        QFS {output_stream=(fn s => TextIO.output(os, s)),
             comdepth=ref 0,
             pardepth=ref 0,
             flush=(fn () => TextIO.flushOut os),
             antiquote=ref false,
             row=ref 0,
             rowstart=ref 0};

     fun loop() = let
       val lexer = filter.makeLexer (read_from_stream is) state
     in
       lexer()
       handle Interrupt => (let open filter.UserDeclarations
                         in
                           #comdepth args := 0;
                           #pardepth args := 0;
                           #antiquote args := false;
                           loop()
                         end)
  end
in
  loop();
  TextIO.closeOut os
end;

val examplesDir = ".";

fun use file =
let
   val filename = FileSys.tmpName()^".hol"
   val _ = unquote_to file filename;
   val _ = PolyML.use filename;
   val _ = FileSys.remove filename
in
   ()
end;
