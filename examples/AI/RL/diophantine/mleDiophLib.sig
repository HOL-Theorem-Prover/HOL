signature mleDiophLib =
sig

  include Abbrev

  type graph = bool list
  val graph_compare : graph * graph -> order
  val graph_to_string : bool list -> string
  val string_to_graph : string -> bool list
  val graph_to_il : bool list -> int list

  type poly = int list list
  val poly_compare : poly * poly -> order
  val ilts : int list -> string
  val stil : string -> int list
  val poly_to_string : poly -> string
  val string_to_poly : string -> poly
  val poly_size : poly -> int

  val modulo : int
  val maxexponent : int
  val maxmonomial : int
  val maxvar : int
  val numberl : int list

  val eval_poly : poly -> int -> int vector -> int
  val random_poly : unit -> poly

  val dioph_set : poly -> int list
  val dioph_match : poly -> bool list -> bool
  val gen_diophset : int -> int -> (int list, poly) Redblackmap.dict ->
    ((int list, poly) Redblackmap.dict * int)
  val term_of_poly : poly -> term
  val human_of_poly : poly -> string
  val veri_of_poly : poly -> term

  val export_data : (int list * poly) list * (int list * poly) list -> unit
  val import_data : string -> (int list * poly) list

end
