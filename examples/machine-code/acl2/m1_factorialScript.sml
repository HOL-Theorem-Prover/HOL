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

val f1 = el 1 (CONJUNCTS defs)
val f2 = el 2 (CONJUNCTS defs)

val _ = save_thm("acl2_fact_definition",defs);
val _ = save_thm("acl2_fact_certificate",th);


(* print result 

open TextIO sexp;

val outstr = openOut "fact.lisp";
fun out s = output(outstr, s);

val _ = print_acl2def out (defun (concl f2));
val _ = print_acl2def out (defun (concl f1));

val _ = flushOut outstr;
val _ = closeOut outstr;

 / print result *)


val _ = export_theory();
