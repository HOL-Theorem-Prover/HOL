signature patriciaLib =
sig

  include Abbrev

  type term_ptree
  type num = Arbnum.num

  val dest_ptree : term -> term_ptree
  val mk_ptree   : term_ptree -> term
  val is_ptree   : term -> bool

  val Define_mk_ptree : string -> term_ptree -> thm
  val Define_mk_ptree_with_is_ptree : string -> term_ptree -> thm * thm

  val empty         : term_ptree
  val peek          : term_ptree -> num -> term option
  val add           : term_ptree -> (num * term) -> term_ptree
  val add_list      : term_ptree -> (num * term) list -> term_ptree
  val remove        : term_ptree -> num -> term_ptree
  val traverse      : term_ptree -> num list
  val keys          : term_ptree -> num list
  val transform     : (term -> term) -> term_ptree -> term_ptree
  val size          : term_ptree -> int
  val depth         : term_ptree -> int
  val every_leaf    : (num -> term -> bool) -> term_ptree -> bool
  val tabulate      : int * (int -> num * term) -> term_ptree
  val in_ptree      : num * term_ptree -> bool
  val insert_ptree  : num * term_ptree -> term_ptree
  val ptree_of_list : (num * term) list -> term_ptree
  val list_of_ptree : term_ptree -> (num * term) list
  val ptree_of_nums : num list -> term_ptree

  val int_peek          : term_ptree -> int -> term option
  val int_add           : term_ptree -> (int * term) -> term_ptree
  val int_add_list      : term_ptree -> (int * term) list -> term_ptree
  val int_remove        : term_ptree -> int -> term_ptree
  val int_in_ptree      : int * term_ptree -> bool
  val int_insert_ptree  : int * term_ptree -> term_ptree
  val int_ptree_of_list : (int * term) list -> term_ptree
  val ptree_of_ints     : int list -> term_ptree

  val string_peek          : term_ptree -> string -> term option
  val string_add           : term_ptree -> (string * term) -> term_ptree
  val string_add_list      : term_ptree -> (string * term) list -> term_ptree
  val string_remove        : term_ptree -> string -> term_ptree
  val string_in_ptree      : string * term_ptree -> bool
  val string_insert_ptree  : string * term_ptree -> term_ptree
  val string_ptree_of_list : (string * term) list -> term_ptree
  val ptree_of_strings     : string list -> term_ptree

  val custom_pp_term_ptree :
    (ppstream -> bool -> unit) -> (ppstream -> num * term -> unit) -> int ->
    ppstream -> term_ptree -> unit

  val pp_term_ptree : ppstream -> term_ptree -> unit

  val PTREE_PEEK_CONV         : conv
  val PTREE_ADD_CONV          : conv
  val PTREE_REMOVE_CONV       : conv
  val PTREE_SIZE_CONV         : conv
  val PTREE_DEPTH_CONV        : conv
  val PTREE_TRANSFORM_CONV    : conv -> conv
  val PTREE_EVERY_LEAF_CONV   : conv -> conv
  val PTREE_EXISTS_LEAF_CONV  : conv -> conv
  val PTREE_IN_PTREE_CONV     : conv
  val PTREE_IS_PTREE_CONV     : conv
  val PTREE_INSERT_PTREE_CONV : conv
  val PTREE_OF_NUMSET_CONV    : conv

  val PTREE_CONV              : conv
  val PTREE_DEFN_CONV         : conv

  val ptree_new_defn_depth : int ref

  val add_ptree_compset : computeLib.compset -> unit
  val ptree_compset     : unit -> computeLib.compset

end
