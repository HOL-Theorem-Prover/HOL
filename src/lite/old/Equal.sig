signature Equal =
sig


   type hol_type = Type.hol_type
   type term = Term.term
   type thm = Thm.thm
   type conv = Abbrev.conv

   (* ------------------------------------------------------------------
    * General syntax for binary operators (nb. monomorphic constructor only).
    *
    * Nb. strip_binop strips only on the right, binops strips both
    * left and right (ala strip_conj and strip_disj).
    * ------------------------------------------------------------------ *)

    val mk_binop : term -> term * term -> term
    val is_binop : term -> term -> bool
    val dest_binop : term -> term -> term * term
    val strip_binop : term -> term -> term list * term
    val binops : term -> term -> term list
    val lhand : term -> term

    val mk_icomb : term * term -> term
    val list_mk_icomb : term -> term list -> term

    (* versions which do not treat negations as implications *)
    val dest_imp : term -> term * term
    val is_imp : term -> bool
    val strip_imp : term -> term list * term;

    val name_of_const : term -> string
    type typ = Type.hol_type
    val --> : typ * typ -> typ;  (* infix synonym for mk_fun_ty *)
    val mk_fun_ty : (typ * typ) -> typ;
    val dest_fun_ty : typ -> (typ * typ);
    val is_fun_ty : typ -> bool;
    val bool_ty : typ;

    val TRY_CONV : conv -> conv
    val ORELSEC : conv * conv -> conv
    val THENC : conv * conv -> conv

    val RIGHT_BETAS : term list -> thm -> thm
    val BINDER_CONV : conv -> conv
    val BINOP_CONV : term -> conv -> conv
    val BODY_CONV : conv -> conv
    val COMB2_CONV : conv -> conv -> conv
    val COMB2_QCONV : conv -> conv -> conv
    val COMB_CONV : conv -> conv
    val COMB_QCONV : conv -> conv

    val LAND_CONV : conv -> conv
    val MK_ABSL_CONV : term list -> conv
    val MK_ABS_CONV : term -> conv
    val MK_BINOP : term -> thm * thm -> thm
    val PINST : (hol_type * hol_type) list -> (term * term) list -> thm -> thm
    val REPEATC : conv -> conv
    val REPEATQC : conv -> conv

    val SUBS_CONV : thm list -> conv
    val SUB_QCONV : conv -> conv
    val SUB_CONV : conv -> conv
    val ABS_CONV : conv -> conv

    val THENCQC : conv * conv -> conv
    val THENQC : conv * conv -> conv

    val SINGLE_DEPTH_CONV : conv -> conv
    val ONCE_DEPTH_CONV : conv -> conv
    val ONCE_DEPTH_QCONV : conv -> conv
    val DEPTH_BINOP_CONV : term -> conv -> conv
    val DEPTH_CONV : conv -> conv
    val DEPTH_QCONV : conv -> conv
    val REDEPTH_CONV : conv -> conv
    val REDEPTH_QCONV : conv -> conv
    val TOP_DEPTH_CONV : conv -> conv
    val TOP_DEPTH_QCONV : conv -> conv
    val TOP_SWEEP_CONV : conv -> conv
    val TOP_SWEEP_QCONV : conv -> conv

   val alpha : term -> term -> term

   val MK_DISJ : thm -> thm -> thm
   val MK_CONJ : thm -> thm -> thm
   val MK_FORALL : term -> thm -> thm
   val MK_EXISTS : term -> thm -> thm

   val SIMPLE_DISJ_CASES : thm -> thm -> thm
   val SIMPLE_CHOOSE : term -> thm -> thm

end (* sig *)

