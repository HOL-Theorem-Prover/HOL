signature hhsTools =
sig

  include Abbrev
  
  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)
  
  val hhs_search_time : Time.time ref
  val hhs_tactic_time : real ref
  
  val hhs_badstacl  : string list ref
  val hhs_stacfea   : (lbl_t, fea_t) Redblackmap.dict ref
  val hhs_cthyfea   : feav_t list ref
  val hhs_ddict     : (goal, feav_t list) Redblackmap.dict ref
  val hhs_ndict     : (string, int) Redblackmap.dict ref
  val mdict_glob    : (string, fea_t) Redblackmap.dict ref
  val negmdict_glob : (string, unit) Redblackmap.dict ref
  val dbfetch_of_string : string -> string
  
  val hhs_mcdict : (int list, (bool * int)) Redblackmap.dict ref
  val hhs_mcdict_cthy : (int list, (bool * int)) Redblackmap.dict ref
  
  
  val clean_feadata : unit -> unit
  val init_stacfea_ddict : feav_t list -> unit
  val update_stacfea_ddict : feav_t -> unit
  
  val tactictoe_dir    : string
  val hhs_feature_dir  : string
  val hhs_code_dir     : string
  val hhs_search_dir   : string
  val hhs_predict_dir  : string
  val hhs_record_dir   : string
  val hhs_open_dir     : string
  val hhs_succrate_dir : string
  val hhs_mdict_dir    : string
  val hhs_mc_dir    : string
  
  val mkDir_err : string -> unit
  val hide_out : ('a -> 'b) -> 'a -> 'b

  val incr   : int ref -> unit
  
  val is_string   : string -> bool
  val is_number   : string -> bool
  val is_chardef  : string -> bool
  val is_reserved : string -> bool
  val drop_sig : string -> string
 
  val dfind  : 'a -> ('a, 'b) Redblackmap.dict -> 'b
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
  
  val findSome : ('a -> 'b option) -> 'a list -> 'b option
  val first_n : int -> 'a list -> 'a list
  val part_n : int -> 'a list -> ('a list * 'a list)
  val number_list : int -> 'a list -> (int * 'a) list

  val sum_real : real list -> real
  val average_real : real list -> real
  val sum_int : int list -> int
  
  val mk_fast_set : ('a * 'a -> order) -> 'a list -> 'a list
  val mk_sameorder_set : ('a * 'a -> order) -> 'a list -> 'a list
  val dict_sort   : ('a * 'a -> order) -> 'a list -> 'a list
  val topo_sort   : (''a * ''a list) list -> ''a list
  
  val mk_string_set : string list -> string list
  val count_dict  : 
    ('a, int) Redblackmap.dict -> 'a list -> ('a, int) Redblackmap.dict
   
  val compare_rmin : (('a * real) * ('a * real)) -> order
  val compare_rmax : (('a * real) * ('a * real)) -> order
  val list_rmax : real list -> real
  
  val goal_compare : (goal * goal) -> order
  val strict_term_compare : (term * term) -> order
  val strict_goal_compare : (goal * goal) -> order
  
  val cpl_compare  : ('a * 'a -> order) -> ('b * 'b -> order) 
                     -> (('a * 'b) * ('a * 'b)) -> order
  val lbl_compare  : (lbl_t * lbl_t) -> order
  val feav_compare : (feav_t * feav_t) -> order
  
  val string_of_goal : goal -> string

  val readl : string -> string list
  val bare_readl : string -> string list
  val readl_empty : string -> string list 
  val append_file : string -> string -> unit
  val write_file : string -> string -> unit
  val erase_file : string -> unit
  val append_endline : string -> string -> unit
  val writel : string -> string list -> unit
  
  val add_time : ('a -> 'b) -> 'a -> 'b * real
  val print_time : string -> real -> unit
  val print_endline : string -> unit
  val total_time : real ref -> ('a -> 'b) -> 'a -> 'b
  
  val debug : string -> unit
  val debug_t : string -> ('a -> 'b) -> 'a -> 'b
  val debug_search : string -> unit
  val debug_proof  : string -> unit
  val debug_parse  : string -> unit
  val debug_replay : string -> unit
  val debug_record : string -> unit

  val split_sl : ''a -> ''a list -> ''a list * ''a list
  val rpt_split_sl : ''a -> ''a list -> ''a list list

  val split_level : string -> string list -> (string list * string list)
  val rpt_split_level : string -> string list -> string list list
  val split_string : string -> string -> (string * string)
  val rm_prefix : string -> string -> string    
  
  val fold_left : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b


end
