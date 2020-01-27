signature mleLib =
sig

  include Abbrev
  
  (* utils *)
  val compare_third :
    ('a * 'b -> order) -> ('d * 'e * 'a) * ('f * 'g * 'b) -> order
  
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

  (* combinator terms *)
  val tag : term -> term
  val cA : term
  val cT : term
  val cS : term
  val cK : term
  val cE : term
  val cX : term
  val cV1 : term
  val cV2 : term
  val cV3 : term
  val cts : term -> string
  val cterm_size : term -> int
  
  (* combinator theorems *)
  val s_thm : term
  val k_thm : term
  val s_thm_tagged : term
  val k_thm_tagged : term
  val s_thm_quant : term
  val k_thm_quant : term
  val left_thm : term
  val right_thm : term
  
  (* combinator others *)
  val mk_cE : term * term -> term
  val lo_cnorm : int -> term list -> term -> term option
  val subst_cmatch : term -> term -> term
  val list_mk_cA : term list-> term
  val strip_cA : term -> term list
  val random_cterm : int -> term
  val cgen_random : int -> (int * int) -> term list 
  val cgen_exhaustive : int -> term list  


end
