signature hhsPredict =
sig

  include Abbrev
  
  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)
  
  val learn_tfidf : ('a * int list) list -> (int, real) Redblackmap.dict

  (* term *)
  val closest_subterm: goal -> term -> term
  
  (* tactic *)
  val stacknn:
    (int, real) Redblackmap.dict -> int -> feav_t list -> fea_t -> lbl_t list

  val stacknn_uniq:
    (int, real) Redblackmap.dict -> int -> feav_t list -> fea_t -> lbl_t list

  val add_stacdesc: 
    (goal, lbl_t list) Redblackmap.dict -> int -> lbl_t list -> lbl_t list
        
  (* thm *)
  val thmknn:
    (int, real) Redblackmap.dict -> int -> (string * fea_t) list -> fea_t -> string list   
  
  val thmknn_std: int -> goal -> string list
  
  val add_thmdep: int -> string list -> string list
  
  val thmknn_wdep: 
   (int, real) Redblackmap.dict -> int -> (string * fea_t) list -> fea_t -> string list
  
  (* goal *)
  val mcknn : 
    (int, real) Redblackmap.dict -> int -> ((bool * int) * int list) list -> 
    int list -> real

end
