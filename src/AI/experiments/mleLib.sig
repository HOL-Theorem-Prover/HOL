signature mleLib =
sig

  include Abbrev

  (* arithmetic *)
  val mk_suc : term -> term
  val mk_sucn : int -> term
  val mk_add : term * term -> term
  val mk_mult : term * term -> term
  val zero : term
  val dest_suc : term -> term
  val dest_add : term -> (term * term)
  val is_suc_only : term -> bool
  val eval_numtm : term -> int

  (* position *)
  type pos = int list
  val string_of_pos : pos -> string
  val pos_of_string : string -> pos
  val subst_pos : term * pos -> term -> term
  val find_subtm : term * pos -> term
  val narg_ge : int -> term * pos -> bool
  val all_pos : term -> pos list
  val all_subtmpos : term -> (term * pos) list

  (* equality *)
  val sym : term -> term
  val paramod_ground : term -> (term * pos) -> term option

  (* arithmetical proof *)
  val robinson_eq_list : term list
  val robinson_eq_vect : term vector
  val lo_trace : int -> term -> ((term * pos) list * int) option
  val lo_prooflength : int -> term -> int

end
