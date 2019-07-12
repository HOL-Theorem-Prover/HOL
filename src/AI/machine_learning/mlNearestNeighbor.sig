signature mlNearestNeighbor =
sig

  include Abbrev

  type lbl = (string * real * goal * goal list)
  type fea = int list

  (* termknn *)
  val termknn:
    (int, real) Redblackmap.dict * (term, fea) Redblackmap.dict -> int ->
    fea -> term list

  (* theorem *)
  val thmknn:
    (int, real) Redblackmap.dict * (string, fea) Redblackmap.dict -> int ->
    fea -> string list

  val thmknn_wdep:
    (int, real) Redblackmap.dict * (string, fea) Redblackmap.dict -> int ->
    fea -> string list

  (* tactic *)
  val stacknn_preselect:
    (int, real) Redblackmap.dict * (lbl * fea) list -> int ->
    fea -> (lbl * fea) list

  val stacknn_uniq:
    (int, real) Redblackmap.dict * (lbl * fea) list -> int ->
    fea -> string list

  val add_stacdep:
    (goal, lbl list) Redblackmap.dict -> int -> lbl list -> lbl list

end
