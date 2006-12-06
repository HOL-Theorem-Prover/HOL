(* ========================================================================= *)
(* PREDICATE SUBTYPE PROVER                                                  *)
(* ========================================================================= *)

signature subtypeTools =
sig

(* ------------------------------------------------------------------------- *)
(* Solver conversions.                                                       *)
(* ------------------------------------------------------------------------- *)

type solver_conv = Conv.conv -> Conv.conv

val cond_rewr_conv : Thm.thm -> solver_conv

val cond_rewrs_conv : Thm.thm list -> solver_conv

val binop_ac_conv :
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
    solver_conv

(* ------------------------------------------------------------------------- *)
(* Named conversions.                                                        *)
(* ------------------------------------------------------------------------- *)

type named_conv = {name : string, key : Term.term, conv : solver_conv}

val named_conv_to_simpset_conv : named_conv -> simpLib.convdata

(* ------------------------------------------------------------------------- *)
(* Subtype contexts.                                                         *)
(* ------------------------------------------------------------------------- *)

val ORACLE : bool ref  (* Use an oracle to solve subtype constraints *)

type context

val empty : context

val add_rewrite : Thm.thm -> context -> context

val add_conversion : named_conv -> context -> context

val add_reduction : Thm.thm -> context -> context

val add_judgement : Thm.thm -> context -> context

val simpset_frag : context -> simpLib.ssfrag

val simpset : context -> simpLib.simpset

val to_string : context -> string

val pp : ppstream -> context -> unit

(* ------------------------------------------------------------------------- *)
(* Subtype context pairs: one for simplification, the other for              *)
(* normalization.                                                            *)
(*                                                                           *)
(* By convention add_X2 adds to both contexts, add_X2' adds to just the      *)
(* simplify context, and add_X2'' adds to just the normalize context.        *)
(* ------------------------------------------------------------------------- *)

type context2

val dest2 : context2 -> {simplify : context, normalize : context}

val empty2 : context2

val add_rewrite2 : Thm.thm -> context2 -> context2
val add_rewrite2' : Thm.thm -> context2 -> context2
val add_rewrite2'' : Thm.thm -> context2 -> context2

val add_conversion2'' : named_conv -> context2 -> context2

val add_reduction2 : Thm.thm -> context2 -> context2

val add_judgement2 : Thm.thm -> context2 -> context2

val simpset_frag2 :
    context2 -> {simplify : simpLib.ssfrag, normalize : simpLib.ssfrag}

val simpset2 :
    context2 -> {simplify : simpLib.simpset, normalize : simpLib.simpset}

val to_string2 : context2 -> string

val pp2 : ppstream -> context2 -> unit

end
