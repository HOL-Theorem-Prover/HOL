signature tttPredict =
sig

  include Abbrev

  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)

  val dependencies_of_thm : thm -> (bool * string list)

  (* tfidf *)
  val learn_tfidf : ('a * int list) list -> (int, real) Redblackmap.dict

  (* term *)
  val termknn: int -> goal -> term -> term list

  (* tactic *)
  val stacknn:
    (int, real) Redblackmap.dict -> int -> feav_t list -> fea_t -> lbl_t list

  val stacknn_uniq:
    (int, real) Redblackmap.dict -> int -> feav_t list -> fea_t -> lbl_t list

  val add_stacdesc:
    (goal, lbl_t list) Redblackmap.dict -> int -> lbl_t list -> lbl_t list

  (* thm (should be sthm) *)
  val all_thmfeav : unit ->
    (int, real) Redblackmap.dict *
    (string * fea_t) list *
    (string, goal * fea_t) Redblackmap.dict

  val thmknn:
    (int, real) Redblackmap.dict * (string * fea_t) list -> int -> fea_t -> string list

  val thmknn_std: int -> goal -> string list

  val thmknn_wdep:
    (int, real) Redblackmap.dict *
    (string * fea_t) list *
    (string, goal * fea_t) Redblackmap.dict ->
    int -> fea_t -> string list

  (* goal *)
  val mcknn :
    (int, real) Redblackmap.dict -> int -> ((bool * int) * int list) list ->
    int list -> real

end
