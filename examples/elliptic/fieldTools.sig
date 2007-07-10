(* ========================================================================= *)
(* FIELD THEORY TOOLS                                                        *)
(* ========================================================================= *)

signature fieldTools =
sig

(* ------------------------------------------------------------------------- *)
(* Syntax operations.                                                        *)
(* ------------------------------------------------------------------------- *)

val field_ty_op : string

val field_inv_tm : Term.term
val dest_field_inv : Term.term -> Term.term * Term.term
val is_field_inv : Term.term -> bool

val field_mult_tm : Term.term
val dest_field_mult : Term.term -> Term.term * Term.term * Term.term
val is_field_mult : Term.term -> bool

val field_exp_tm : Term.term
val dest_field_exp : Term.term -> Term.term * Term.term * Term.term
val is_field_exp : Term.term -> bool

(* ------------------------------------------------------------------------- *)
(* AC normalization.                                                         *)
(* ------------------------------------------------------------------------- *)

val field_add_ac_conv : subtypeTools.named_conv

val field_mult_ac_conv : subtypeTools.named_conv

(* ------------------------------------------------------------------------- *)
(* Proof tools.                                                              *)
(* ------------------------------------------------------------------------- *)

val ORACLE_field_poly : bool ref

val field_div_elim_ss : subtypeTools.context2 -> simpLib.simpset

val field_poly_ss : subtypeTools.context2 -> Thm.thm list -> simpLib.simpset

val field_poly_basis_ss : subtypeTools.context2 -> simpLib.simpset

(* ------------------------------------------------------------------------- *)
(* Subtype context.                                                          *)
(* ------------------------------------------------------------------------- *)

val field_context : subtypeTools.context2

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val field_pretty_print : bool ref

val field_pretty_print_max_size : int ref

end
