signature arm_evalLib =
sig
   include Abbrev

   val ARMe_CONV            : conv
   val ARM_ASSEMBLE_CONV    : conv

   val hol_assemble1        : term -> Arbnum.num -> term frag list -> term
   val hol_assemble         : term -> Arbnum.num -> term frag list list -> term
   val list_assemble        : term -> string list -> term
   val assemble1            : term -> string -> term
   val assemble             : term -> string -> term

   val set_registers        : term -> term -> term
   val set_status_registers : term -> term -> term

   val load_mem  : string -> int -> Arbnum.num -> term -> term
   val save_mem  : string -> Arbnum.num -> Arbnum.num -> bool -> term -> unit

   val init      : term -> term -> term -> thm
   val next      : thm -> thm
   val eval      : int -> term -> term -> term -> thm list
   val evaluate  : int -> term -> term -> term -> thm
end
