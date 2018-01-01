(* this is an -*- sml -*- file *)
(* this file gets executed by buildheap *)


infix ++
fun p1 ++ p2 = OS.Path.concat(p1,p2)
val target = Systeml.HOLDIR ++ "bin" ++ "mkmunge.exe"

val outstrm = TextIO.openOut target;
fun TD s = Systeml.protect (Systeml.HOLDIR ++ "src" ++ "TeX" ++ s);

TextIO.output(outstrm, "#!/bin/sh\n");
TextIO.output(outstrm,
              Systeml.protect (Systeml.HOLDIR ++ "bin" ++ "buildheap") ^
              " \"$@\" --exe main --defaultout munge.exe " ^
              String.concatWith " "
                   (map TD ["mungeTools", "munger.lex.sml", "holindex",
                            "mkmunger.sml", "poly-mkmunger.ML"]) ^ "\n");

TextIO.closeOut outstrm;

Systeml.mk_xable target;
