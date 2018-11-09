signature anotherLib =
sig

  include Abbrev

  type lbl = (string * real * goal * goal list)
  type fea = int list

  (* misc *)
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
  val rmDir_err : string -> unit
  val rmDir_rec : string -> unit
  val cleanDir_rec : string -> unit
  val clean_dir : string -> unit
  val run_cmd : string -> unit
  val cmd_in_dir : string -> string -> unit
  val exists_file : string -> bool

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
  val dset : ('a * 'a -> order) -> 'a list -> 
    ('a, unit) Redblackmap.dict
  val daddset : 
    'a list -> 'b -> ('a, unit) Redblackmap.dict -> 
    ('a, unit) Redblackmap.dict
  val distrib : ('a * 'b list) list -> ('a * 'b) list
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
  val mk_sameorder_set : ('a * 'a -> order) -> 'a list -> 'a list
  val dict_sort : ('a * 'a -> order) -> 'a list -> 'a list
  val topo_sort : (''a * ''a list) list -> ''a list
  val sort_thyl : string list -> string list
  val fold_left : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val mk_batch : int -> 'a list -> 'a list list
  val number_partition : int -> int -> int list list   
  val duplicate : int -> 'a list -> 'a list  
  val indent: int -> string   

  (* random *)
  val random_real : unit -> real
  val shuffle   : 'a list -> 'a list
  val select_in_distrib : ('a * real) list -> 'a

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
  val writel_path : string -> string -> string list -> unit
  val debug_flag  : bool ref
  val debug_in_dir : string -> string -> string -> unit

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
  
  (* reserved *)
  val is_quoted   : string -> bool
  val is_number   : string -> bool
  val is_chardef  : string -> bool
  val is_reserved : string -> bool

  (* statistics *)
  val incr   : int ref -> unit
  val decr   : int ref -> unit
  val sum_real : real list -> real
  val average_real : real list -> real
  val standard_deviation : real list -> real
  val sum_int : int list -> int
  val int_div : int -> int -> real
  val pow : real -> int -> real
  val approx : int -> real -> real
  val percent : real -> real  

  (* term *)
  val rename_bvarl : (string -> string) -> term -> term
  val all_bvar : term -> term list
  val strip_type : hol_type -> (hol_type list * hol_type)
  val has_boolty : term -> bool  
  val only_concl : thm -> term

end
