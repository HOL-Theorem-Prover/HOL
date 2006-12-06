(* ========================================================================= *)
(* GROUP THEORY TOOLS                                                        *)
(* ========================================================================= *)

signature groupTools =
sig

(* ------------------------------------------------------------------------- *)
(* Syntax operations.                                                        *)
(* ------------------------------------------------------------------------- *)

val group_inv_tm : Term.term
val dest_group_inv : Term.term -> Term.term * Term.term
val is_group_inv : Term.term -> bool

val group_mult_tm : Term.term
val dest_group_mult : Term.term -> Term.term * Term.term * Term.term
val is_group_mult : Term.term -> bool

val group_exp_tm : Term.term
val dest_group_exp : Term.term -> Term.term * Term.term * Term.term
val is_group_exp : Term.term -> bool

(* ------------------------------------------------------------------------- *)
(* AC normalization.                                                         *)
(* ------------------------------------------------------------------------- *)

val group_ac_conv : subtypeTools.named_conv

(* ------------------------------------------------------------------------- *)
(* Subtype context.                                                          *)
(* ------------------------------------------------------------------------- *)

val group_context : subtypeTools.context2

end
