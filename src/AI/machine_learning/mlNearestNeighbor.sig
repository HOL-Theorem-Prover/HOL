signature mlNearestNeighbor =
sig

  include Abbrev

  type lbl = (string * real * goal * goal list)
  type fea = int list

  (* theorem 
  val all_thmfeav : unit ->
    (int, real) Redblackmap.dict *
    (string * fea) list *
    (string, goal * fea) Redblackmap.dict
  *)
  
  val thmknn:
    (int, real) Redblackmap.dict * (string * fea) list -> int -> 
    fea -> string list

  (*
  val thmknn_std: int -> goal -> string list

  val thmknn_wdep:
    (int, real) Redblackmap.dict *
    (string * fea) list *
    (string, goal * fea) Redblackmap.dict ->
    int -> fea -> string list
  *)

  (* tactic *)
  val stacknn_preselect:
    (int, real) Redblackmap.dict -> int -> (lbl * fea) list -> fea -> 
    (lbl * fea) list

  val stacknn_uniq:
    (int, real) Redblackmap.dict -> int -> (lbl * fea) list -> fea -> 
    lbl list

  (*
   val add_stacdesc:
    (goal, lbl list) Redblackmap.dict -> int -> lbl list -> lbl list
  *)

end
