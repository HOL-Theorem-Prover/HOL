signature tttTools =
sig

  include Abbrev

  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)

  val ttt_new_theory_suffix : string

  val ttt_search_time : Time.time ref
  val ttt_tactic_time : real ref

  (* directory *)
  val tactictoe_dir    : string

  val ttt_tacfea_dir   : string
  val ttt_thmfea_dir   : string
  val ttt_glfea_dir    : string

  val ttt_code_dir     : string
  val ttt_open_dir     : string

  val ttt_search_dir   : string
  val ttt_record_dir   : string
  val ttt_unfold_dir   : string

  (* commands *)
  val mkDir_err        : string -> unit
  val rmDir_rec        : string -> unit
  val run_cmd          : string -> unit
  val cmd_in_dir       : string -> string -> unit
  val exists_file      : string -> bool

  (* hiding output of a function *)
  val hide_out : ('a -> 'b) -> 'a -> 'b

  (* tactictoe globals *)
  val clean_tttdata : unit -> unit
    (* tactic *)
  val ttt_tacerr      : string list ref
  val ttt_tacfea      : (lbl_t, fea_t) Redblackmap.dict ref
  val ttt_tacfea_cthy : (lbl_t, fea_t) Redblackmap.dict ref
  val ttt_tacdep      : (goal, lbl_t list) Redblackmap.dict ref
  val ttt_taccov      : (string, int) Redblackmap.dict ref
    (* theorem *)
  val ttt_thmfea      : (goal, (string * fea_t)) Redblackmap.dict ref
    (* goal list *)
  val ttt_glfea       : (int list, (bool * int)) Redblackmap.dict ref
  val ttt_glfea_cthy  : (int list, (bool * int)) Redblackmap.dict ref

  (* theorem data *)
  val namespace_tag : string
  val dbfetch_of_string : string -> string
  val mk_metis_call : string list -> string

  (* dictionnary *)
  val dfind  : 'a -> ('a, 'b) Redblackmap.dict -> 'b
  val dfind_err : string -> 'a -> ('a, 'b) Redblackmap.dict -> 'b
  val dmem   : 'a -> ('a, 'b) Redblackmap.dict -> bool
  val drem   : 'a -> ('a, 'b) Redblackmap.dict -> ('a, 'b) Redblackmap.dict
  val dadd   :
    'a -> 'b -> ('a, 'b) Redblackmap.dict -> ('a, 'b) Redblackmap.dict
  val daddl  :
    ('a * 'b) list -> ('a, 'b) Redblackmap.dict -> ('a, 'b) Redblackmap.dict
  val dempty : ('a * 'a -> order) -> ('a, 'b) Redblackmap.dict
  val dnew   : ('a * 'a -> order) -> ('a * 'b) list -> ('a, 'b) Redblackmap.dict
  val dlist  : ('a, 'b) Redblackmap.dict -> ('a * 'b) list
  val dlength : ('a, 'b) Redblackmap.dict -> int
  val dapp : ('a * 'b -> unit) -> ('a, 'b) Redblackmap.dict -> unit
  val dkeys : ('a, 'b) Redblackmap.dict -> 'a list

  val mk_string_set : string list -> string list
  val count_dict  :
    ('a, int) Redblackmap.dict -> 'a list -> ('a, int) Redblackmap.dict

  (* list *)
  val findSome : ('a -> 'b option) -> 'a list -> 'b option
  val first_n : int -> 'a list -> 'a list
  val first_test_n : ('a -> bool) -> int -> 'a list -> 'a list
  val part_n : int -> 'a list -> ('a list * 'a list)
  val number_list : int -> 'a list -> (int * 'a) list
  val list_diff : ''a list -> ''a list -> ''a list
  val mk_fast_set : ('a * 'a -> order) -> 'a list -> 'a list
  val mk_sameorder_set : ('a * 'a -> order) -> 'a list -> 'a list
  val dict_sort   : ('a * 'a -> order) -> 'a list -> 'a list
  val topo_sort   : (''a * ''a list) list -> ''a list
  val sort_thyl   : string list -> string list
  val fold_left : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b

  (* statistics *)
  val incr   : int ref -> unit
  val decr   : int ref -> unit
  val sum_real : real list -> real
  val average_real : real list -> real
  val sum_int : int list -> int
  val compare_rmin : (('a * real) * ('a * real)) -> order
  val compare_rmax : (('a * real) * ('a * real)) -> order
  val list_rmax : real list -> real

  (* time *)
  val add_time : ('a -> 'b) -> 'a -> 'b * real
  val print_time : string -> real -> unit
  val print_endline : string -> unit
  val total_time : real ref -> ('a -> 'b) -> 'a -> 'b

  (* compare *)
  val goal_compare : (goal * goal) -> order
  val strict_term_compare : (term * term) -> order
  val strict_goal_compare : (goal * goal) -> order
  val cpl_compare  : ('a * 'a -> order) -> ('b * 'b -> order)
                     -> (('a * 'b) * ('a * 'b)) -> order
  val lbl_compare  : (lbl_t * lbl_t) -> order
  val feav_compare : (feav_t * feav_t) -> order

  (* input/output *)
  val string_of_goal : goal -> string
  val string_of_bool : bool -> string
  val readl : string -> string list
  val bare_readl : string -> string list
  val readl_empty : string -> string list
  val append_file : string -> string -> unit
  val write_file : string -> string -> unit
  val erase_file : string -> unit
  val append_endline : string -> string -> unit
  val writel : string -> string list -> unit

  (* debug *)
  val debug : string -> unit
  val debug_t : string -> ('a -> 'b) -> 'a -> 'b
  val debug_err : string -> 'a
  val set_debugsearch : bool -> unit
  val debug_search : string -> unit
  val debug_proof  : string -> unit
  val debug_parse  : string -> unit
  val debug_replay : string -> unit
  val debug_record : string -> unit
  val ttt_unfold_cthy : string ref
  val debug_unfold : string -> unit

  (* parse *)
  val is_string   : string -> bool
  val is_number   : string -> bool
  val is_chardef  : string -> bool
  val is_reserved : string -> bool

  val drop_sig : string -> string
  val unquote_string : string -> string
  val split_sl : ''a -> ''a list -> ''a list * ''a list
  val rpt_split_sl : ''a -> ''a list -> ''a list list
  val split_level : string -> string list -> (string list * string list)
  val rpt_split_level : string -> string list -> string list list
  val split_string : string -> string -> (string * string)
  val remove_string : string -> string -> string
  val rm_prefix : string -> string -> string
  val rm_squote : string -> string
  val rm_space  : string -> string




end
