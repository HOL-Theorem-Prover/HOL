
val num = mk_thy_type{Thy = "num", Tyop = "num", Args = []};

new_constant ("rd", bool);
new_constant ("n", bool --> bool --> bool);
new_constant ("x", bool --> num);
new_constant ("size", alpha --> bool --> num);

load (valOf (OS.Process.getEnv "TESTLIB")) handle _ => OS.Process.exit OS.Process.failure;

val t = Parse.Term ‘x’;

if is_const t andalso type_of t = “:bool -> num” then ()
else (print "Type or const-ness of \"x\" incorrect!\n";
      OS.Process.exit OS.Process.failure);
