signature aiLib =
sig

  include Abbrev

  (* misc *)
  type fea = int list
  type lbl = (string * real * goal * goal list)
  val number_fst : int -> 'a list -> (int * 'a) list
  val number_snd : int -> 'a list -> ('a * int) list
  val print_endline : string -> unit
  val vector_to_list : 'a vector -> 'a list
  val hash_string : string -> int

  (* comparisons *)
  val cpl_compare :
    ('a * 'b -> order) ->
    ('c * 'd -> order) ->
    ('a * 'c) * ('b * 'd) -> order
  val goal_compare : (goal * goal) -> order
  val lbl_compare : (lbl * lbl) -> order
  val compare_rmin : (('a * real) * ('a * real)) -> order
  val compare_rmax : (('a * real) * ('a * real)) -> order
  val compare_imin : (('a * int) * ('a * int)) -> order
  val compare_imax : (('a * int) * ('a * int)) -> order
  val list_rmax : real list -> real
  val list_imax : int list -> int

  (* time *)
  val add_time : ('a -> 'b) -> 'a -> 'b * real
  val print_time : string -> real -> unit
  val total_time : real ref -> ('a -> 'b) -> 'a -> 'b

  (* commands *)
  val mkDir_err : string -> unit
  val run_cmd : string -> unit
  val cmd_in_dir : string -> string -> unit
  val exists_file : string -> bool
  val remove_file : string -> unit

  (* dictionnary *)
  val dfind  : 'a -> ('a, 'b) Redblackmap.dict -> 'b
  val dmem   : 'a -> ('a, 'b) Redblackmap.dict -> bool
  val drem   : 'a -> ('a, 'b) Redblackmap.dict -> ('a, 'b) Redblackmap.dict
  val dadd   :
    'a -> 'b -> ('a, 'b) Redblackmap.dict -> ('a, 'b) Redblackmap.dict
  val daddl  :
    ('a * 'b) list -> ('a, 'b) Redblackmap.dict -> ('a, 'b) Redblackmap.dict
  val dempty : ('a * 'a -> order) -> ('a, 'b) Redblackmap.dict
  val dnew   : ('a * 'a -> order) -> ('a * 'b) list ->
    ('a, 'b) Redblackmap.dict
  val dlist  : ('a, 'b) Redblackmap.dict -> ('a * 'b) list
  val dlength : ('a, 'b) Redblackmap.dict -> int
  val dapp : ('a * 'b -> unit) -> ('a, 'b) Redblackmap.dict -> unit
  val dkeys : ('a, 'b) Redblackmap.dict -> 'a list
  val dmap  : ('a * 'b -> 'c) ->
    ('a, 'b) Redblackmap.dict -> ('a, 'c) Redblackmap.dict
  val dfoldl : ('a * 'b * 'c -> 'c) -> 'c -> ('a, 'b) Redblackmap.dict -> 'c
  val inv_dict :
    ('a * 'a -> order) ->
    ('b, 'a) Redblackmap.dict -> ('a, 'b) Redblackmap.dict
  val dregroup : ('a * 'a -> order) -> ('a * 'b) list ->
    ('a, 'b list) Redblackmap.dict
  val distrib : ('a * 'b list) list -> ('a * 'b) list
  val dappend : 'a * 'b ->
    ('a, 'b list) Redblackmap.dict -> ('a, 'b list) Redblackmap.dict
  val dappendl : ('a * 'b) list ->
    ('a, 'b list) Redblackmap.dict -> ('a, 'b list) Redblackmap.dict
  val dconcat : ('a * 'a -> order) ->
    ('a, 'b list) Redblackmap.dict list -> ('a, 'b list) Redblackmap.dict

  val dset : ('a * 'a -> order) -> 'a list ->
    ('a, unit) Redblackmap.dict
  val daddset : 'a list ->
    ('a, unit) Redblackmap.dict -> ('a, unit) Redblackmap.dict
  val union_dict : ('a * 'a -> order) ->
     ('a, 'b) Redblackmap.dict list -> ('a, 'b) Redblackmap.dict
  val count_dict :
    ('a, int) Redblackmap.dict -> 'a list -> ('a, int) Redblackmap.dict

  (* list *)
  val only_hd : 'a list -> 'a
  val one_in_n : int -> int -> 'a list -> 'a list
  val map_snd : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list
  val map_fst : ('a -> 'b) -> ('a * 'c) list -> ('b * 'c) list
  val map_assoc : ('a -> 'b) -> 'a list -> ('a * 'b) list
  val cartesian_product : 'a list -> 'b list -> ('a * 'b) list
  val cartesian_productl : 'a list list -> 'a list list
  val findSome  : ('a -> 'b option) -> 'a list -> 'b option
  val first_n   : int -> 'a list -> 'a list
  val first_test_n : ('a -> bool) -> int -> 'a list -> 'a list
  val part_n : int -> 'a list -> ('a list * 'a list)
  val number_list : int -> 'a list -> (int * 'a) list
  val list_diff : ''a list -> ''a list -> ''a list
  val subset : ''a list -> ''a list -> bool
  val mk_fast_set : ('a * 'a -> order) -> 'a list -> 'a list
  val mk_string_set : string list -> string list
  val mk_term_set : term list -> term list
  val mk_type_set : hol_type list -> hol_type list
  val mk_sameorder_set : ('a * 'a -> order) -> 'a list -> 'a list
  val dict_sort : ('a * 'a -> order) -> 'a list -> 'a list
  val topo_sort : ('a * 'a -> order) -> ('a * 'a list) list -> 'a list
  val sort_thyl : string list -> string list
  val fold_left : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val mk_batch : int -> 'a list -> 'a list list
  val cut_n : int -> 'a list -> 'a list list
  val number_partition : int -> int -> int list list
  val duplicate : int -> 'a list -> 'a list
  val indent: int -> string
  (* todo check if list_combine and transpose_ll do the same thing *)
  val list_combine : 'a list list -> 'a list list
  val combine_triple : 'a list * 'b list * 'c list -> ('a * 'b * 'c) list
  val split_triple : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
  val quintuple_of_list : 'a list -> 'a * 'a * 'a * 'a * 'a

  (* random *)
  val random_real : unit -> real
  val shuffle   : 'a list -> 'a list
  val random_elem : 'a list -> 'a
  val random_int : (int * int) -> int (* slow uses random_elem *)
  val select_in_distrib : ('a * real) list -> 'a
  val random_percent : real -> 'a list -> 'a list * 'a list

  (* input/output *)
  val string_of_goal : goal -> string
  val trace_tacl : tactic list -> goal -> unit
  val string_of_bool : bool -> string
  val readl : string -> string list
  val bare_readl : string -> string list
  val readl_empty : string -> string list
  val append_file : string -> string -> unit
  val write_file : string -> string -> unit
  val erase_file : string -> unit
  val append_endline : string -> string -> unit
  val writel : string -> string list -> unit
  val writel_path : string -> string -> string list -> unit
  val debug_flag  : bool ref
  val debug_in_dir : string -> string -> string -> unit
  val stream_to_string :
    string -> (TextIO.outstream -> unit) -> string list

  (* parse *)
  val unquote_string : string -> string
  val drop_sig : string -> string
  val split_sl : ''a -> ''a list -> ''a list * ''a list
  val rpt_split_sl : ''a -> ''a list -> ''a list list
  val split_level : string -> string list -> (string list * string list)
  val rpt_split_level : string -> string list -> string list list
  val split_string : string -> string -> (string * string)
  val rm_prefix : string -> string -> string
  val rm_squote : string -> string
  val rm_space  : string -> string
  datatype lisp = Lterm of lisp list | Lstring of string
  val lisp_of : string list -> lisp list
  val rec_fun_type : int -> hol_type -> hol_type
  val term_of_lisp : lisp -> term

  (* escape *)
  val escape : string -> string
  val unescape : string -> string

  (* statistics *)
  val incr   : int ref -> unit
  val decr   : int ref -> unit
  val sum_real : real list -> real
  val average_real : real list -> real
  val standard_deviation : real list -> real
  val sum_int : int list -> int
  val int_div : int -> int -> real
  val int_pow : int -> int -> int
  val bin_rep : int -> int -> real list
  val pow : real -> int -> real
  val approx : int -> real -> real
  val percent : real -> real
  val pad : int -> string -> string -> string

  (* term *)
  val rename_bvarl : (string -> string) -> term -> term
  val rename_allvar : term -> term
  val all_bvar : term -> term list
  val strip_type : hol_type -> (hol_type list * hol_type)
  val has_boolty : term -> bool
  val only_concl : thm -> term

  (* printing *)
  val tts : term -> string
  val its : int -> string
  val rts : real -> string

  (* thread *)
  val interruptkill : Thread.thread -> unit

  (* neural network units *)
  val oper_compare : (term * int) * (term * int) -> order
  val operl_of : term -> (term * int) list

  (* position *)
  type pos = int list
  val subst_pos : term * pos -> term -> term
  val find_subtm : term * pos -> term
  val narg_ge : int -> term * pos -> bool
  val all_pos : term -> pos list
 
  (* arithmetic *)
  val mk_suc : term -> term
  val mk_sucn : int -> term
  val mk_add : term * term -> term
  val mk_mult : term * term -> term
  val zero : term
  val dest_suc : term -> term
  val dest_add : term -> (term * term)
  val is_suc_only : term -> bool

  (* equality *)
  val sym : term -> term
  val paramod_ground : term -> (term * pos) -> term option



end
