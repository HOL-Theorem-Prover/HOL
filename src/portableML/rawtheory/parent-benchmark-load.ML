(* Source-only setup using the existing standalone raw-theory tool loader.
   Run from src/portableML/rawtheory. Generated lexer/parser sources must
   already exist (as they do after a normal HOL build). This does not call
   DatPrinter.main or compile an executable. *)
use "mkdatprinter.ML";
use "../TheoryDat.sig";
use "../TheoryDat.sml";
use "parent-benchmark.ML";
