open testutils


val _ = tprint "Testing Holmake VAR=value command-line variable assignments:";
fun do_holmake args =
  OS.Process.system
    ("cd test && " ^
     Systeml.protect (Systeml.HOLDIR ^ "/bin/Holmake") ^ " --holstate " ^
     Systeml.protect (Systeml.HOLDIR ^ "/bin/hol.state0") ^ " " ^ args);

val _ = tprint "1. Good: successful assignment";
val res = do_holmake
  "-r INBETWEEN=YES RECURSIVE=also_YES.321 TEST1=SET";
val _ = if OS.Process.isSuccess res then OK() else die ""; (* check output *)

val _ = tprint "2. Good: specific target";
val res = do_holmake "ARULE=IGNORE A_RULE A_RULE=IGNORE";
val _ = if OS.Process.isSuccess res then OK() else die ""; (* check output *)

val _ = tprint "3. Bad: Holmake foo=";
val res = do_holmake "foo= A_RULE";
val _ = if OS.Process.isSuccess res then die"" else OK();

val _ = tprint "4. Bad: Holmake =foo";
val res = do_holmake "=foo A_RULE";
val _ = if OS.Process.isSuccess res then die"" else OK();

val _ = tprint "5. Bad: Holmake = foo";
val res = do_holmake "= foo A_RULE";
val _ = if OS.Process.isSuccess res then die"" else OK();

val _ = tprint "6. Bad: Holmake foo=bar=";
val res = do_holmake "foo=bar= A_RULE";
val _ = if OS.Process.isSuccess res then die"" else OK();

val _ = tprint "7. Bad: Holmake =bar=foo=";
val res = do_holmake "=bar=foo= A_RULE";
val _ = if OS.Process.isSuccess res then die"" else OK();

val _ = tprint "8. Bad: Holmake bar==foo";
val res = do_holmake "bar==foo A_RULE";
val _ = if OS.Process.isSuccess res then die"" else OK();

