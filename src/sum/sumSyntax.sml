structure sumSyntax :> sumSyntax =
struct

local open sumTheory in end;

open HolKernel Abbrev;

val ERR = mk_HOL_ERR "sumSyntax"

fun mk_sum (ty1, ty2) =
   mk_thy_type {Tyop = "sum", Thy = "sum", Args = [ty1, ty2]}

fun dest_sum ty =
   case total dest_thy_type ty of
      SOME {Tyop = "sum", Thy = "sum", Args = [ty1, ty2]} => (ty1, ty2)
    | other => raise ERR "dest_sum" "not a sum type"

val strip_sum = strip_binop (total dest_sum)
val spine_sum = spine_binop (total dest_sum)
val list_mk_sum = end_itlist (curry mk_sum)

val sum_case_tm =
   mk_thy_const
      {Name = "sum_CASE",
       Thy = "sum",
       Ty = mk_sum (beta, gamma) --> (beta --> alpha) -->
            (gamma --> alpha) --> alpha}

fun mk_sum_case (f, g, s) =
   let
      val (df, r) = dom_rng (type_of f)
      val (dg, _) = dom_rng (type_of g)
   in
      list_mk_comb
         (inst [alpha |-> r, beta |-> df, gamma |-> dg] sum_case_tm, [s, f, g])
   end

val monop = HolKernel.syntax_fns "sum" 1 HolKernel.dest_monop HolKernel.mk_monop

val (isl_tm, mk_isl, dest_isl, is_isl) = monop "ISL"
val (isr_tm, mk_isr, dest_isr, is_isr) = monop "ISR"
val (outl_tm, mk_outl, dest_outl, is_outl) = monop "OUTL"
val (outr_tm, mk_outr, dest_outr, is_outr) = monop "OUTR"

val (inl_tm, mk_inl, dest_inl, is_inl) =
   HolKernel.syntax_fns "sum" 1
      (fn tm1 => fn e => fn t =>
          (HolKernel.dest_monop tm1 e t, snd (dest_sum (type_of t))))
      (fn tm => fn (t, ty) =>
          Term.mk_comb
             (Term.inst [Type.alpha |-> type_of t, Type.beta |-> ty] tm, t))
      "INL"

val (inr_tm, mk_inr, dest_inr, is_inr) =
   HolKernel.syntax_fns "sum" 1
      (fn tm1 => fn e => fn t =>
          (HolKernel.dest_monop tm1 e t, fst (dest_sum (type_of t))))
      (fn tm => fn (t, ty) =>
          Term.mk_comb
             (Term.inst [Type.alpha |-> ty, Type.beta |-> type_of t] tm, t))
      "INR"

(*---------------------------------------------------------------------------*)
(* Lifting sums                                                              *)
(*---------------------------------------------------------------------------*)

datatype ('a,'b) sum = INL of 'a | INR of 'b

fun lift_sum ty =
   let
      val inl = TypeBasePure.cinst ty inl_tm
      val inr = TypeBasePure.cinst ty inr_tm
      fun lift f g (INL x) = mk_comb(inl, f x)
        | lift f g (INR y) = mk_comb(inr, g y)
   in
      lift
   end

end
