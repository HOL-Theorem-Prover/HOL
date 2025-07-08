(* Moscow ML magic to make interrupts appear as the Interrupt exception *)
prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

fun die_with s = (
  TextIO.output(TextIO.stdErr, s ^ "\n");
  OS.Process.exit OS.Process.failure
)

val _ = linkToSigobj.main()
        handle Interrupt => die_with "linkToSigobj interrupted"
             | e => die_with ("Holmake failed with exception: " ^
                              exnMessage e)
~
