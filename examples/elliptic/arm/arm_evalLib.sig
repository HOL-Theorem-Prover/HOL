signature arm_evalLib =
sig
   include Abbrev

   type mode
   type arm_state

   val ARM_CONV             : conv
   val ARM_RULE             : rule
   val ARM_ASSEMBLE_CONV    : conv
   val SORT_SUBST_CONV      : conv
   val SORT_FSUBST_CONV     : conv
   val SORT_BSUBST_CONV     : conv

   val hol_assemble1        : term -> Arbnum.num -> term frag list -> term
   val hol_assemble         : term -> Arbnum.num -> term frag list list -> term
   val list_assemble        : term -> string list -> term
   val assemble1            : term -> string -> term
   val assemble             : term -> string -> term

   val empty_memory         : term
   val empty_registers      : term
   val empty_psrs           : term

   val set_registers        : term -> term -> term
   val set_status_registers : term -> term -> term

   val dest_arm_eval    : term -> arm_state

   val print_all_regs   : term -> unit
   val print_usr_regs   : term -> unit
   val print_std_regs   : term -> unit
   val print_regs       : (int * mode) list -> term -> unit
   val print_mem_range  : term -> Arbnum.num * int -> unit
   val print_mem_block  : term -> int -> unit

   val load_mem  : string -> int -> Arbnum.num -> term -> term
   val save_mem  : string -> Arbnum.num -> Arbnum.num -> bool -> term -> unit

   val init      : term -> term -> term -> thm
   val next      : thm -> thm
   val eval      : int * term * term * term -> thm list
   val evaluate  : int * term * term * term -> thm
end
