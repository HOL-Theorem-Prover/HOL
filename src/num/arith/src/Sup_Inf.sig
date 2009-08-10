signature Sup_Inf =
sig
  type int = Arbint.int

  datatype bound = Bound of Rationals.rat * (string * Rationals.rat) list
                 | Max_bound of bound list
                 | Min_bound of bound list
                 | Pos_inf
                 | Neg_inf
  type internal_bound
  val SIMP : internal_bound -> bound
  val SUP : (int * (string * int) list) list ->
            (bound * (string list)) ->
            internal_bound
  val INF : (int * (string * int) list) list ->
            (bound * (string list)) ->
            internal_bound
  val eval_bound : bound -> bound
  val SUP_INF :
         (int * (string * int) list) list -> (string * bound * bound) list
end
