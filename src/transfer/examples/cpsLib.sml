structure cpsLib :> cpsLib =
struct

open HolKernel boolLib
open Abbrev
open cpsTheory

val contify_t = prim_mk_const {Thy = "cps", Name = "contify"}
val cwc_t = prim_mk_const {Thy = "cps", Name = "cwc"}

fun cwcp t0 =
    let
      val t = gen_tyvarify t0
      val (dom,rng) = dom_rng (type_of t)
      val x = numvariant (free_vars t) (mk_var ("x", dom))
      val tx = mk_comb(t,x)
      val k = numvariant (free_vars t) (mk_var("k", rng --> gen_tyvar()))
      val eqn0 = mk_eq(list_mk_icomb(cwc_t, [tx, k]), mk_comb(k, tx))
      val tyvs = type_vars_in_term eqn0
      val eqn =
          inst (ListPair.map (fn (old,new) => old |-> new)
                             (tyvs, tyvar_sequence (length tyvs)))
               eqn0
    in
      PART_MATCH I cwc_def eqn
    end

fun contify_CONV ths0 t =
  let val (f,xs) = strip_comb t
      val ths = contify_option_case :: contify_pair_case ::
                contify_list_case :: ths0
  in
    if same_const f contify_t then
      if length xs = 2 then
        FIRST_CONV
          (map (fn th => REWR_CONV th THENC REDEPTH_CONV BETA_CONV) ths) t
        handle HOL_ERR _ =>
          let val t0 = last xs
              val base = (REWR_CONV contify_def THENC TRY_CONV BETA_CONV)
          in
            if is_var t0 then base t
            else if is_const t0 then base t
            else if numSyntax.is_numeral t0 then base t
            else if is_cond t0 then REWR_CONV contify_COND t
            else if is_comb t0 then REWR_CONV contify_app t
            else NO_CONV t
          end
      else NO_CONV t
    else if is_abs t then ETA_CONV t
    else NO_CONV t
  end



end
