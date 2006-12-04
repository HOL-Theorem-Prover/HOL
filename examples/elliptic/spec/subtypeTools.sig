(* ========================================================================= *)
(* PREDICATE SUBTYPE PROVER                                                  *)
(* ========================================================================= *)

signature subtypeTools =
sig

val ORACLE_algebra_dproc : bool ref

type algebraContext

val alg_context : algebraContext

val alg_add_rewrite : Thm.thm -> algebraContext -> algebraContext
val alg_add_rewrite' : Thm.thm -> algebraContext -> algebraContext
val alg_add_rewrite'' : Thm.thm -> algebraContext -> algebraContext

val alg_add_conversion'' :
    {conv : Conv.conv -> Conv.conv, key : Term.term, name : string} ->
    algebraContext -> algebraContext

val alg_add_reduction : Thm.thm -> algebraContext -> algebraContext

val alg_add_judgement : Thm.thm -> algebraContext -> algebraContext

val alg_simpset_frags :
    algebraContext -> {simplify : simpLib.ssfrag, normalize : simpLib.ssfrag}

val alg_simpsets :
    algebraContext -> {simplify : simpLib.simpset, normalize : simpLib.simpset}

val alg_pp : ppstream -> algebraContext -> unit

val alg_binop_ac_conv :
    {term_compare : Term.term * Term.term -> order,
     dest_binop : Term.term -> Term.term * Term.term * Term.term,
     dest_inv : Term.term -> Term.term * Term.term,
     dest_exp : Term.term -> Term.term * Term.term * Term.term,
     assoc_th : Thm.thm,
     comm_th : Thm.thm,
     comm_th' : Thm.thm,
     id_ths : Thm.thm list,
     simplify_ths : Thm.thm list,
     combine_ths : Thm.thm list,
     combine_ths' : Thm.thm list} ->
    Conv.conv -> Conv.conv

end
