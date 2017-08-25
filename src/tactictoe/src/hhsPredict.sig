signature hhsPredict =
sig

  include Abbrev
  
  type lbl_t = (string * real * goal * goal list)
  type fea_t = string list
  type feav_t = (lbl_t * fea_t)
  
  val learn_tfidf : ('a * string list) list -> (string, real) Redblackmap.dict

  val stacknn:
    (string, real) Redblackmap.dict -> int ->  feav_t list -> fea_t -> 
    (lbl_t * real) list
    
  val thmknn:
    (string, real) Redblackmap.dict -> int -> (string * fea_t) list -> fea_t -> 
    (string * real) list   

  val stacknn_ext : int -> feav_t list -> fea_t -> feav_t list
  
  val thmknn_ext :
    int -> (string * fea_t * string list) list -> fea_t -> string list

end
