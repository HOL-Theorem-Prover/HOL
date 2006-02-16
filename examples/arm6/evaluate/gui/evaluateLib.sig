signature evaluateLib =
sig
   include Abbrev

   val mem_blocks      : unit -> word list
   val mem_rm_block    : word -> unit
   val mem_nth_block   : int -> word
   val mem_read_block  : word -> {data : Arbnum.num array, key : word} option
   val mem_print_block : word -> unit
   val mem_read        : bool option -> Arbnum.num -> Arbnum.num
   val mem_write       : bool -> Arbnum.num -> Arbnum.num -> unit
   val mem_read_word   : Arbnum.num -> Arbnum.num

   val block_start : word -> Arbnum.num
   val block_range : word -> string

   val read_trace  : thm list -> (({exc : term, ireg : term, psrs : term array,
                       registers : term * term patriciaLib.ptree} *
                       term) * term list) list
   val reg_string  : word -> string

   val eval_word   : term -> Arbnum.num
   val mk_word     : Arbnum.num -> term

   val load_data   : string -> int -> Arbnum.num -> unit
   val save_data   : string -> Arbnum.num -> Arbnum.num -> bool -> unit

   val assemble    : Arbnum.num -> string list -> unit
   val assemble1   : Arbnum.num -> string -> unit

   val SUBST_RULE  : rule

   val init_state6 : term -> {done : bool, newinst : bool, state : thm}
   val next_state6 : (bool * Arbnum.num) option -> thm ->
                     {done : bool, newinst : bool,
                      pending : (bool * Arbnum.num) option, state : thm}
   val state6      : int -> term -> thm list

   val init_state  : term -> {done : bool, state : thm}
   val next_state  : thm -> {done : bool, state : thm}
   val state       : int -> term -> thm list
end
