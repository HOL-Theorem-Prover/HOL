signature robddLib =
sig
  type robdd   = Robdd.robdd
  type term    = Term.term
  type 'a net  = 'a Net.net
  type thm     = Thm.thm
  type conv    = Abbrev.conv
  type tactic  = Abbrev.tactic
  type var_map = (string, int) Binarymap.dict
  type table   = int * var_map
  type bdd_map = (term, robdd) Polyhash.hash_table * term net

  (* HOL term operations *)
  val term_to_bdd : term -> robdd
  val bdd_to_cond : robdd -> term
  val find_model  : term -> term
  val bddCheck    : term -> bool option
  val find_refutation : term -> term

  (* HOL Inference rules *)
  val mk_bdd_thm : term -> thm  (* oracle *)
  val BDD_MATCH_CONV : bdd_map -> term -> conv
  val BDD_CONV : bdd_map -> conv
  val BDD_TAC : tactic

  (* robdd operations *)
  val NodeCount : robdd -> int
  val is_taut   : robdd -> bool
  val find_bdd_model : robdd -> robdd option
  val find_bdd_refutation : robdd -> robdd option

  (* var_map operations *)
  val empty_var_map : var_map
  val size : var_map -> int
  val var_to_int : var_map -> string -> int
  val lookup_var : var_map -> string -> robdd
  val peek_map : var_map -> string -> int option
  val findAssignment : var_map * robdd -> term
  val bdd_to_literal : var_map -> robdd -> term
  val var_map_to_pairs : var_map -> (string * int) list
  val subst_bdd : var_map -> (string * string) list -> robdd -> robdd
  val show_var_map : unit -> (string * int) list

  (* table operations *)
  val empty_table : table
  val add_var_to_table : string * table -> table
  val add_vars_to_table : table -> term list -> table

  (* bdd_map operations *)
  val current_bdd_map : bdd_map
  val NetPeek : var_map -> bdd_map -> term -> robdd option
  val BDD_TR : bdd_map -> term -> term
  val fromTerm : var_map -> bdd_map -> term -> robdd
  val show_bdd_map : unit -> (term * robdd) list

  (* state *)
  val bdd_state : (table * bdd_map) ref
  val reset_state : string list -> unit
  val get_var_order : unit -> string list
  val add_var : string -> int
  val add_definition 
     : thm -> table * bdd_map -> (term * robdd) * (table * bdd_map)
  val add_defn : thm -> term * robdd
  val get_node_name : int -> string

  (* printing *)
  val default_dot_dir : string ref
  val print_state : unit -> (term * robdd) list
  val print_bdd_state : string -> table * bdd_map -> (term * robdd) list
  val showTerm : term -> robdd * (string * int) list
  val showBDD : string -> string -> robdd -> robdd
  val showBDDofTerm : string -> string -> var_map -> bdd_map 
                        -> term -> robdd * (string * int) list

end
