signature arm_evalLib =
sig
   include Abbrev

   type mode
   type sys_state
   type sys_state3

   val arm_compset          : computeLib.compset
   val ARM_CONV             : conv
   val ARM_RULE             : rule
   val ARM_ASSEMBLE_CONV    : conv
   val SORT_UPDATE_CONV     : conv

   val list_assemble        : term -> string list -> term
   val assemble1            : term -> string -> term
   val assemble             : term -> string -> term

   val empty_memory         : term
   val empty_registers      : term
   val empty_psrs           : term

   val set_registers        : term -> term frag list -> term
   val set_status_registers : term -> term frag list -> term

   val print_all_regs       : term -> unit
   val print_usr_regs       : term -> unit
   val print_std_regs       : term -> unit
   val print_regs           : (int * mode) list -> term -> unit
   val print_mem_range      : term -> Arbnum.num * int -> unit
   val print_mem_block      : term -> int -> unit

   val load_mem     : string -> int -> Arbnum.num -> term -> term
   val save_mem     : string -> Arbnum.num -> Arbnum.num -> bool -> term -> unit

   val dest_state   : term -> sys_state
   val mk_state     : sys_state -> term

   val init         : term * term * term * term -> sys_state -> thm
   val next         : (term * term * term * term) -> thm -> thm

   val eval_cp      : int * (term * term * term * term) * sys_state -> thm list
   val evaluate_cp  : int * (term * term * term * term) * sys_state -> thm

   val eval         : int * term * term * term -> thm list
   val evaluate     : int * term * term * term -> thm

   val dest_state3  : term -> sys_state3
   val mk_state3    : sys_state3 -> term

   val init3        : term * term * term * term -> sys_state3 -> thm
   val next3        : (term * term * term * term) -> thm -> thm

   val eval_cp3     : int * (term * term * term * term) * sys_state3 -> thm list
   val evaluate_cp3 : int * (term * term * term * term) * sys_state3 -> thm

   val eval3        : int * term * term * term -> thm list
   val evaluate3    : int * term * term * term -> thm
end
