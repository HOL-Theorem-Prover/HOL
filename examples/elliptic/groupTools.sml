(* ========================================================================= *)
(* GROUP THEORY TOOLS                                                        *)
(* ========================================================================= *)

structure groupTools :> groupTools =
struct

open HolKernel Parse boolLib bossLib groupTheory;

(* ------------------------------------------------------------------------- *)
(* Syntax operations.                                                        *)
(* ------------------------------------------------------------------------- *)

val group_inv_tm = ``group_inv``;

fun dest_group_inv tm =
    let
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm group_inv_tm orelse raise ERR "group_inv_neg" ""
    in
      (f,x)
    end;

val is_group_inv = can dest_group_inv;

val group_mult_tm = ``group_mult``;

fun dest_group_mult tm =
    let
      val (tm,y) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm group_mult_tm orelse raise ERR "dest_group_mult" ""
    in
      (f,x,y)
    end;

val is_group_mult = can dest_group_mult;

val group_exp_tm = ``group_exp``;

fun dest_group_exp tm =
    let
      val (tm,n) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm group_exp_tm orelse raise ERR "dest_group_exp" ""
    in
      (f,x,n)
    end;

val is_group_exp = can dest_group_exp;

(* ------------------------------------------------------------------------- *)
(* AC normalization.                                                         *)
(* ------------------------------------------------------------------------- *)

val group_ac_conv =
    {name = "group_ac_conv",
     key = ``g.mult x y``,
     conv = subtypeTools.binop_ac_conv
              {term_compare = compare,
               dest_binop = dest_group_mult,
               dest_inv = dest_group_inv,
               dest_exp = dest_group_exp,
               assoc_th = group_assoc,
               comm_th = group_comm,
               comm_th' = group_comm',
               id_ths = [],
               simplify_ths = [],
               combine_ths = [],
               combine_ths' = []}};

(* ------------------------------------------------------------------------- *)
(* Subtype context.                                                          *)
(* ------------------------------------------------------------------------- *)

val context = subtypeTools.empty2;
val context = subtypeTools.add_judgement2 AbelianGroup_Group context;
val context = subtypeTools.add_judgement2 FiniteGroup_Group context;
val context = subtypeTools.add_judgement2 FiniteAbelianGroup_FiniteGroup context;
val context =
    subtypeTools.add_judgement2 FiniteAbelianGroup_AbelianGroup context;
val context = subtypeTools.add_reduction2 group_id_carrier context;
val context = subtypeTools.add_reduction2 group_inv_carrier context;
val context = subtypeTools.add_reduction2 group_mult_carrier context;
val context = subtypeTools.add_rewrite2 group_lid context;
val context = subtypeTools.add_rewrite2 group_linv context;
val context = subtypeTools.add_rewrite2'' group_assoc context;
val context = subtypeTools.add_rewrite2 group_rinv context;
val context = subtypeTools.add_rewrite2 group_rid context;
val context = subtypeTools.add_rewrite2' group_lcancel context;
val context = subtypeTools.add_rewrite2' group_lcancel_id context;
val context = subtypeTools.add_rewrite2' group_rcancel context;
val context = subtypeTools.add_rewrite2' group_rcancel_id context;
val context = subtypeTools.add_rewrite2' group_inv_cancel context;
val context = subtypeTools.add_rewrite2 group_inv_inv context;
val context = subtypeTools.add_rewrite2 group_inv_id context;
val context = subtypeTools.add_rewrite2'' group_inv_mult context;
val context = subtypeTools.add_reduction2 group_exp_carrier context;
val context = subtypeTools.add_rewrite2 group_id_exp context;
val context = subtypeTools.add_conversion2'' group_ac_conv context;
val context = subtypeTools.add_reduction2 trivial_group context;
val context = subtypeTools.add_reduction2 add_mod context;
val context = subtypeTools.add_judgement2 Prime_Nonzero context;
val context = subtypeTools.add_reduction2 mult_mod context;

val group_context = context

end
