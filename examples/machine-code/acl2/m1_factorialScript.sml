open HolKernel Parse boolLib bossLib;

val _ = new_theory "m1_factorial";


val (th,defs) = m1_progLib.decompile_m1 "fact" `
  List [sym "M1" "ICONST"; nat 1]
  List [sym "M1" "ISTORE"; nat 1]
  List [sym "M1" "ILOAD"; nat 0]
  List [sym "M1" "IFLE"; nat 10]
  List [sym "M1" "ILOAD"; nat 0]
  List [sym "M1" "ILOAD"; nat 1]
  List [sym "M1" "IMUL"]
  List [sym "M1" "ISTORE"; nat 1]
  List [sym "M1" "ILOAD"; nat 0]
  List [sym "M1" "ICONST"; nat 1]
  List [sym "M1" "ISUB"]
  List [sym "M1" "ISTORE"; nat 0]
  List [sym "M1" "GOTO"; int (-10)]
  List [sym "M1" "ILOAD"; nat 1]`

val _ = save_thm("acl2_fact_definition",defs);
val _ = save_thm("acl2_fact_certificate",th);


(* export result *)

val f1 = el 1 (CONJUNCTS defs);
val f2 = el 2 (CONJUNCTS defs);

val outstr = TextIO.openOut "fact.lisp";
fun out s = TextIO.output(outstr, s);

val _ = sexp.current_package := "M1";
val _ = sexp.print_acl2def out (sexp.defun (concl f2));
val _ = sexp.print_acl2def out (sexp.defun (concl f1));

val _ = TextIO.flushOut outstr;
val _ = TextIO.closeOut outstr;


val _ = export_theory();
