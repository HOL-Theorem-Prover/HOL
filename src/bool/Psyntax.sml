structure Psyntax :> Psyntax =
struct

open Feedback HolKernel;

val mk_type       = Type.mk_type
val dest_type     = Type.dest_type
val mk_var        = Term.mk_var
val mk_const      = Term.mk_const
val mk_comb       = Term.mk_comb
val mk_abs        = Term.mk_abs
val mk_primed_var = Term.mk_primed_var
val dest_var      = Term.dest_var
val dest_const    = Term.dest_const
val dest_comb     = Term.dest_comb
val dest_abs      = Term.dest_abs
val mk_eq         = boolSyntax.mk_eq
val mk_imp        = boolSyntax.mk_imp
val mk_forall     = boolSyntax.mk_forall
val mk_exists     = boolSyntax.mk_exists
val mk_exists1    = boolSyntax.mk_exists1
val mk_select     = boolSyntax.mk_select
val mk_conj       = boolSyntax.mk_conj
val mk_disj       = boolSyntax.mk_disj
val mk_cond       = boolSyntax.mk_cond
val mk_let        = boolSyntax.mk_let
val dest_eq       = boolSyntax.dest_eq
val dest_imp      = boolSyntax.dest_imp
val dest_imp_only = boolSyntax.dest_imp_only
val dest_select   = boolSyntax.dest_select
val dest_forall   = boolSyntax.dest_forall
val dest_exists   = boolSyntax.dest_exists
val dest_exists1  = boolSyntax.dest_exists1
val dest_conj     = boolSyntax.dest_conj
val dest_disj     = boolSyntax.dest_disj
val dest_cond     = boolSyntax.dest_cond
val dest_let      = boolSyntax.dest_let
val new_type      = boolSyntax.new_type
val new_constant  = boolSyntax.new_constant
val new_infix     = boolSyntax.new_infix
val new_binder    = boolSyntax.new_binder


datatype lambda = datatype HolKernel.lambda

val dest_term = HolKernel.dest_term

end; (* Psyntax *)
