(*---------------------------------------------------------------------------
        OS-sensitive build options for the Robdd library.
 ---------------------------------------------------------------------------*)

val CFLAGS = 
   case OS
    of "linux"   => SOME " -Dunix -O3 -rdynamic $(OPTS) $(CINCLUDE)"
     | "solaris" => SOME " -Dunix -O3 $(OPTS) $(CINCLUDE)"
     |     _     => NONE


val DLLIBCOMP =
   case OS
    of "linux"   => SOME "gcc -shared -Wl,-soname,$@ -o $@  $^ $(LIBS)"
     | "solaris" => SOME "ld -G -B dynamic -o $@  $^ $(LIBS)"
     |    _      => NONE

val ALL = 
  if OS="linux" orelse OS="solaris"
  then SOME "$(SMLOBJ) $(SIGOBJ) $(DLLIB)"
  else NONE;