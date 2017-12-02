signature hhsPredict =
sig

  include Abbrev
  
  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)
  
  val learn_tfidf : ('a * int list) list -> (int, real) Redblackmap.dict

  val closest_subterm: goal -> term -> term
  
  val stacknn:
    (int, real) Redblackmap.dict -> int -> feav_t list -> fea_t -> 
    (lbl_t * real) list
    
  val thmknn:
    (int, real) Redblackmap.dict -> int -> (string * fea_t) list -> fea_t -> 
    (string * real) list   
  
  val premcknn : 
    (int, real) Redblackmap.dict -> int -> ((bool * int) * int list) list -> 
    int list -> ((bool * int) * int list) list

  val mcknn : 
    (int, real) Redblackmap.dict -> int -> ((bool * int) * int list) list -> 
    int list -> real
  
  val stacknn_ext : int -> feav_t list -> fea_t -> feav_t list
  
  val thmknn_ext :
    int -> (string * fea_t * string list) list -> fea_t -> string list

  val thmmepo_ext :
    int -> (string * fea_t * string list) list -> fea_t -> string list

end
