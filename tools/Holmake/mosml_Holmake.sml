(* Moscow ML magic to make interrupts appear as the Interrupt exception *)
prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true;

val die_with = Holmake.die_with

val _ = Holmake.main()
        handle Interrupt => die_with "Holmake interrupted"
             | e => die_with ("Holmake failed with exception: " ^
                              exnMessage e)
