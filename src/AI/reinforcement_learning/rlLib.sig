signature rlLib =
sig

  include Abbrev

  type pos = int list

  (* neural network units *)
  val oper_compare : (term * int) * (term * int) -> order
  val operl_of : term -> (term * int) list

  (* position *)
  val subst_pos : term * pos -> term -> term
  val find_subtm : term * pos -> term
  val narg_ge : int -> term * pos -> bool

  (* arithmetic *)
  val mk_suc : term -> term
  val mk_sucn : int -> term
  val mk_add : term * term -> term
  val mk_mult : term * term -> term
  val zero : term
  val dest_suc : term -> term
  val dest_add : term -> (term * term)

  (* equality *)
  val sym : term -> term

  (* higher-order *)
  val let_rw : term -> term



end
