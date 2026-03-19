(* Bring Interrupt into top-level scope so that bare "Interrupt" in pattern
   matches (e.g., in Portable.sml) refers to the exception constructor rather
   than being parsed as a fresh variable. The same binding inside
   MLSYSPortable is also needed because Portable.sml re-exports it as
   MLSYSPortable.Interrupt. *)
exception Interrupt = SML90.Interrupt;
