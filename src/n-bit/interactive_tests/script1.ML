load "wordsTheory";
hide "<<";
load "wordsLib";
structure foo = wordsLib;
val os = TextIO.openOut "test1";
val _ = (TextIO.output(os, "test1 OK\n"); TextIO.closeOut os);
