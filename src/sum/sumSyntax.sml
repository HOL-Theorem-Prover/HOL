structure sumSyntax :> sumSyntax =
struct

local open sumTheory in end;

open HolKernel Abbrev; infix |->;

val ERR = mk_HOL_ERR "sumSyntax";

fun mk_sum(ty1,ty2) = mk_thy_type{Tyop="sum", Thy="sum", Args=[ty1,ty2]};

fun dest_sum ty =
  case total dest_thy_type ty
   of SOME{Tyop="sum", Thy="sum", Args=[ty1,ty2]} => (ty1,ty2)
    | other => raise ERR "dest_sum" "not a sum type";

val strip_sum = strip_binop (total dest_sum);
val spine_sum = spine_binop (total dest_sum);
val list_mk_sum = end_itlist (curry mk_sum);


val inl_tm      = prim_mk_const{Name="INL",      Thy = "sum"}
val inr_tm      = prim_mk_const{Name="INR",      Thy = "sum"}
val isl_tm      = prim_mk_const{Name="ISL",      Thy = "sum"}
val isr_tm      = prim_mk_const{Name="ISR",      Thy = "sum"}
val outl_tm     = prim_mk_const{Name="OUTL",     Thy = "sum"}
val outr_tm     = prim_mk_const{Name="OUTR",     Thy = "sum"}
val sum_case_tm = prim_mk_const{Name="sum_case", Thy = "sum"};

fun mk_inl(tm,ty) = mk_comb(inst[alpha|-> type_of tm, beta |-> ty] inl_tm, tm);

fun mk_inr(tm,ty) = mk_comb(inst[beta|-> type_of tm, alpha |-> ty] inr_tm, tm);

val mk_isl =
  let val (ty,_) = dom_rng(type_of isl_tm)
  in fn tm => mk_comb (inst (match_type ty (type_of tm)) isl_tm, tm)
  end

val mk_isr =
  let val (ty,_) = dom_rng(type_of isr_tm)
  in fn tm => mk_comb (inst (match_type ty (type_of tm)) isr_tm, tm)
  end

val mk_outl =
  let val (ty,_) = dom_rng(type_of outl_tm)
  in fn tm => mk_comb (inst (match_type ty (type_of tm)) outl_tm, tm)
  end

val mk_outr =
  let val (ty,_) = dom_rng(type_of outr_tm)
  in fn tm => mk_comb (inst (match_type ty (type_of tm)) outr_tm, tm)
  end

fun mk_sum_case (f,g,s) =
  let val (df,r) = dom_rng (type_of f)
      val (dg,_) = dom_rng (type_of g)
  in list_mk_comb
       (inst [alpha |-> r, beta |-> df, gamma |-> dg] sum_case_tm, [f,g,s])
  end;

(*---------------------------------------------------------------------------*)
(* Lifting sums                                                              *)
(*---------------------------------------------------------------------------*)

datatype ('a,'b)sum = INL of 'a | INR of 'b;

fun lift_sum ty =
  let val inl = TypeBasePure.cinst ty inl_tm
      val inr = TypeBasePure.cinst ty inr_tm
      fun lift f g (INL x) = mk_comb(inl, f x)
        | lift f g (INR y) = mk_comb(inr, g y)
  in lift
  end

end
