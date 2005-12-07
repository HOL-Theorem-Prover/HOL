signature arm_evalLib =
sig
   include Abbrev

   val ARMe_CONV            : conv

   val assemble1            : term -> Arbnum.num -> string -> term
   val assemble             : term -> Arbnum.num -> string list -> term
   val disassemble1         : term -> Arbnum.num -> string
   val disassemble          : int -> term -> Arbnum.num -> string list

   val set_registers        : term -> term -> term
   val set_status_registers : term -> term -> term

   val load_mem  : string -> int -> Arbnum.num -> term -> term
   val save_mem  : string -> Arbnum.num -> Arbnum.num -> bool -> term -> unit
   val list_mem  : int -> term -> Arbnum.num -> unit

   val init      : term -> term -> term -> thm
   val next      : thm -> thm
   val eval      : int -> term -> term -> term -> thm list
   val evaluate  : int -> term -> term -> term -> thm
end
