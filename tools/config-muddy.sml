(*---------------------------------------------------------------------------
        OS-sensitive build options for the Muddy library.
 ---------------------------------------------------------------------------*)

val CFLAGS =
   case OS
    of "linux"   => SOME " -Dunix -O3 -fPIC $(CINCLUDE)"
     | "solaris" => SOME " -Dunix -O3 $(CINCLUDE)"
     |     _     => NONE


val DLLIBCOMP =
   case OS
    of "linux"   => SOME "ld -shared -o $@ $(COBJS) $(LIBS)"
     | "solaris" => SOME "ld -G -B dynamic -o $@ $(COBJS) $(LIBS)"
     |    _      => NONE

(*
val ALL =
  if OS="linux" orelse OS="solaris"
  then SOME "$(SMLOBJ) $(SIGOBJ) muddy.so"
  else NONE;
*)
val ALL =
  if OS="linux" orelse OS="solaris"
  then SOME " muddy.so"
  else NONE;



