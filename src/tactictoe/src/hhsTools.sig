signature hhsTools =
sig

  include Abbrev
  
  val tactictoe_dir   : string
  val hhs_code_dir    : string
  val hhs_log_dir     : string
  val hhs_predict_dir : string
  val hhs_record_dir  : string

  val dfind  : 'a -> ('a, 'b) Redblackmap.dict -> 'b
  val dmem   : 'a -> ('a, 'b) Redblackmap.dict -> bool
  val drem   : 'a -> ('a, 'b) Redblackmap.dict -> ('a, 'b) Redblackmap.dict
  val dadd   : 'a -> 'b -> 
               ('a, 'b) Redblackmap.dict -> ('a, 'b) Redblackmap.dict
  val dempty : ('a * 'a -> order) -> ('a, 'b) Redblackmap.dict
  
  val first_n : int -> 'a list -> 'a list
  val number_list : int -> 'a list -> (int * 'a) list

  val mk_fast_set : ('a * 'a -> order) -> 'a list -> 'a list
  val dict_sort   : ('a * 'a -> order) -> 'a list -> 'a list
  val mk_string_set : string list -> string list
  val count_dict  : 
    ('a, int) Redblackmap.dict -> 'a list -> ('a, int) Redblackmap.dict
   
  val goal_compare : (goal * goal) -> order
  val string_of_goal : goal -> string

  val readl : string -> string list

end
