signature NumInequalityCoeffs =
sig
   type num = NumType.num
   type term = Term.term

   datatype inequality_relation = Eq | Leq | Less
   val dest_ineq : term -> inequality_relation * (term * term)
   val mk_ineq : inequality_relation -> (term * term) -> term
   val coeff_of_const : (num * (string * num) list) -> num
   val coeffs_of_vars : (num * (string * num) list) -> (string * num) list
   val coeff_of_var : string -> (num * (string * num) list) -> num
   val var_on_left : string -> (num * (string * num) list) -> bool
   val var_on_right : string -> (num * (string * num) list) -> bool
   val var_not_present : string -> (num * (string * num) list) -> bool
   val scale_coeffs : num ->
                      (num * (string * num) list) ->
                      (num * (string * num) list)
   val negate_coeffs : (num * (string * num) list) ->
                       (num * (string * num) list)
   val merge_coeffs : (num * (string * num) list) ->
                      (num * (string * num) list) ->
                      (num * (string * num) list)
   val lhs_coeffs : (num * (string * num) list) -> (num * (string * num) list)
   val rhs_coeffs : (num * (string * num) list) -> (num * (string * num) list)
   val diff_of_coeffs :
          ((num * (string * num) list) * (num * (string * num) list)) ->
          ((num * (string * num) list) * (num * (string * num) list))
   val vars_of_coeffs : (num * (string * num) list) list -> string list
   val var_of_prod : term -> string
   val coeffs_of_arith : term -> (num * (string * num) list)
   val coeffs_of_ineq :
          term -> inequality_relation * (num * (string * num) list)
   val coeffs_of_ineq_set :
          term -> (inequality_relation * (num * (string * num) list)) list
   val coeffs_of_goal : (term list * term) ->
                        inequality_relation * (num * (string * num) list)
   val arith_of_coeffs : num * (string * num) list -> term
   val ineq_of_coeffs :
          inequality_relation * (num * (string * num) list) -> term
end;
