signature aiLib =
sig

  include Abbrev

  (* misc *)
  val number_fst : int -> 'a list -> (int * 'a) list
  val number_snd : int -> 'a list -> ('a * int) list
  val print_endline : string -> unit
  val vector_to_list : 'a vector -> 'a list
  val hash_string : string -> int
  val hash_string_mod : int -> string -> int

  (* comparisons *)
  val cpl_compare :
    ('a * 'b -> order) ->
    ('c * 'd -> order) ->
    ('a * 'c) * ('b * 'd) -> order
  val triple_compare :
    ('a * 'b -> order) ->
    ('c * 'd -> order) ->
    ('e * 'f -> order) ->
    ('a * 'c * 'e) * ('b * 'd * 'f) -> order
  val fst_compare : ('a * 'b -> 'c) -> ('a * 'd) * ('b * 'e) -> 'c
  val snd_compare : ('a * 'b -> 'c) -> ('d * 'a) * ('e * 'b) -> 'c
  val goal_compare : goal * goal -> order
  val compare_rmin : (('a * real) * ('a * real)) -> order
  val compare_rmax : (('a * real) * ('a * real)) -> order
  val compare_imin : (('a * int) * ('a * int)) -> order
  val compare_imax : (('a * int) * ('a * int)) -> order
  val list_rmax : real list -> real
  val list_imax : int list -> int
  val vector_max : ('a -> real) -> 'a vector -> (int * real)
  val vector_maxi : ('a -> real) -> 'a vector -> int
  val vector_mini : ('a -> real) -> 'a vector -> int
  val list_imin : int list -> int
  val tmsize_compare : term * term -> order
  val all_subterms : term -> term list
  val div_equal : int -> int -> int list

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
  val clean_dir : string -> unit

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
  val is_singleton : 'a list -> bool
  val range : (int * int) * (int -> 'a) -> 'a list
  val one_in_n : int -> int -> 'a list -> 'a list
  val map_snd : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list
  val map_fst : ('a -> 'b) -> ('a * 'c) list -> ('b * 'c) list
  val map_assoc : ('a -> 'b) -> 'a list -> ('a * 'b) list
  val all_pairs : 'a list -> ('a * 'a) list
  val cartesian_product : 'a list -> 'b list -> ('a * 'b) list
  val cartesian_productl : 'a list list -> 'a list list
  val findSome  : ('a -> 'b option) -> 'a list -> 'b option
  val first_n   : int -> 'a list -> 'a list
  val first_test_n : ('a -> bool) -> int -> 'a list -> 'a list
  val part_n : int -> 'a list -> ('a list * 'a list)
  val part_pct :  real -> 'a list -> 'a list * 'a list
  val part_group : int list -> 'a list -> 'a list list
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
  val mk_batch_full : int -> 'a list -> 'a list list
  val cut_n : int -> 'a list -> 'a list list
  val cut_modulo : int -> 'a list -> 'a list list
  val number_partition : int -> int -> int list list
  val duplicate : int -> 'a list -> 'a list
  val indent: int -> string
  val list_combine : 'a list list -> 'a list list
  val combine_triple : 'a list * 'b list * 'c list -> ('a * 'b * 'c) list
  val split_triple : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
  val quintuple_of_list : 'a list -> 'a * 'a * 'a * 'a * 'a
  val interleave : int -> 'a list -> 'a list -> 'a list
  val inter_increasing : int list -> int list -> int list
  val best_n : ('a * 'a -> order) -> int -> 'a list -> 'a list
  val best_n_rmaxu : ('a * 'a -> order) -> int -> ('a * real) list -> 'a list

  (* randomness, probability and distributions *)
  val random_real : unit -> real
  val shuffle   : 'a list -> 'a list
  val random_elem : 'a list -> 'a
  val random_int : (int * int) -> int (* uses random_elem *)
  val random_subset : int -> 'a list -> 'a list
  val mk_cumul : ('a * real) list -> ('a * real) list * real
  val select_in_cumul : ('a * real) list * real -> 'a
  val select_in_distrib : ('a * real) list -> 'a
  val select_in_distrib_seeded : real -> ('a * real) list -> 'a
  val best_in_distrib : ('a * real) list -> 'a
  val uniform_proba : int -> real list
  val normalize_proba : real list -> real list
  val uniform_distrib : 'a  list -> ('a * real) list
  val normalize_distrib : ('a * real) list -> ('a * real) list

  (* input/output *)
  val reall_to_string : real list -> string
  val realll_to_string : real list list -> string
  val string_to_reall : string -> real list
  val string_to_realll : string -> real list list
  val string_of_goal : goal -> string
  val string_of_goal_noquote : goal -> string
  val trace_tacl : tactic list -> goal -> unit
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
  val debug : string -> unit
  val debugf : string -> ('a -> string) -> 'a -> unit
  val stream_to_string :
    string -> (TextIO.outstream -> unit) -> string list
  val write_texgraph :
    string -> string * string -> (int * int) list -> unit
  val readl_rm : string -> string list
  val writel_atomic : string -> string list -> unit
  val listDir : string -> string list
  val listDir_all : string -> string list

  (* parse *)
  val hd_string : string -> char
  val tl_string : string -> string
  val unquote_string : string -> string
  val drop_sig : string -> string
  val subst_sl : (string * string) -> string list -> string list
  val split_sl : ''a -> ''a list -> ''a list * ''a list
  val rpt_split_sl : ''a -> ''a list -> ''a list list
  val split_level : string -> string list -> (string list * string list)
  val rpt_split_level : string -> string list -> string list list
  val split_string : string -> string -> (string * string)
  val rm_prefix : string -> string -> string
  val rm_squote : string -> string
  val rm_space  : string -> string
  datatype lisp = Lterm of lisp list | Lstring of string
  val lisp_lexer : string -> string list
  val lisp_parser : string -> lisp list
  val term_of_lisp : lisp -> term

  (* escape *)
  val escape : string -> string
  val unescape : string -> string

  (* statistics *)
  val incr : int ref -> unit
  val decr : int ref -> unit
  val sum_real : real list -> real
  val average_real : real list -> real
  val average_int: int list -> real
  val standard_deviation : real list -> real
  val absolute_deviation : real list -> real
  val sum_int : int list -> int
  val int_div : int -> int -> real
  val int_pow : int -> int -> int
  val int_product : int list -> int
  val bin_rep : int -> int -> real list
  val pow : real -> int -> real
  val approx : int -> real -> real
  val percent : real -> real
  val pad : int -> string -> string -> string
  val tts : term -> string
  val its : int -> string
  val rts : real -> string
  val bts : bool -> string
  val string_to_bool : string -> bool
  val rts_round : int -> real -> string
  val pretty_real : real -> string
  val epsilon : real
  val interval : real -> real * real -> real list
  val gamma_noise_gen : real -> unit -> real

  (* term *)
  val rename_bvarl : (string -> string) -> term -> term
  val rename_allvar : term -> term
  val all_bvar : term -> term list
  val strip_type : hol_type -> (hol_type list * hol_type)
  val strip_type_n : int -> hol_type -> (hol_type list * hol_type)
  val rpt_fun_type : int -> hol_type -> hol_type
  val has_boolty : term -> bool
  val only_concl : thm -> term
  val list_mk_binop : term -> term list -> term
  val strip_binop : term -> term -> term list
  val arity_of : term -> int

  (* term data *)
  val enc_real : real -> HOLsexp_dtype.t
  val dec_real : HOLsexp_dtype.t -> real option
  val write_tmdata :
    ((term -> HOLsexp_dtype.t) -> 'a HOLsexp.encoder) * ('a -> term list) ->
    string -> 'a -> unit
  val read_tmdata :
    ((HOLsexp_dtype.t -> term option) -> HOLsexp_dtype.t -> 'a option) ->
    string -> 'a
  val write_data : ('a -> HOLsexp_dtype.t) -> string -> 'a -> unit
  val read_data : (HOLsexp_dtype.t -> 'a option) -> string -> 'a
  val export_terml : string -> term list -> unit
  val import_terml : string -> term list
  val export_goal : string -> goal -> unit
  val import_goal : string -> goal

  (* sigobj *)
  val sigobj_theories : unit -> string list
  val load_sigobj : unit -> unit
  val link_sigobj : string -> unit

end
