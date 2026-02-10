(*---------------------------------------------------------------------------*)
(* Getting rid of lambdas in a HOL term                                      *)
(* Steps:                                                                    *)
(*                                                                           *)
(* 1. For each occurrence of a lambda (\x.t) in a term, define a function    *)
(*    "fn = \x.t" and replace (\x.t) by fn. Proceed bottom-up.               *)
(*                                                                           *)
(* 2. Note that we have to account for free vars in body of t. Let           *)
(*    FV(\x.t) = v1,...,vk. Define "fn v1 ... vk = \x.t" and replace         *)
(*    (\x.t) by "fn v1...vk".                                                *)
(*                                                                           *)
(* 3. The new definitions have to be normalized so there are no lambdas on   *)
(*    the RHS.                                                               *)
(*---------------------------------------------------------------------------*)

structure Elim_Lambda :> Elim_Lambda =
struct

open HolKernel boolLib bossLib

val ERR = mk_HOL_ERR "Elim_Lambda";

fun with_counter {init,inc} f x =
  let val num_stream = Portable.make_counter{init=init,inc=inc}
  in f num_stream x
  end

local
  val def_prefix = "Fn_"
  fun defName_of i = def_prefix^Int.toString i
  val num_stream = Portable.make_counter{init=0,inc=1}
in
fun new_defVar ty = mk_var(defName_of(num_stream()), ty)

fun is_defVar v =
   String.isPrefix def_prefix $ fst $ dest_var v
   handle HOL_ERR _ => false
end;

val def_list = ref [] : thm list ref

fun find_defs thm =
  let val () = def_list := []
      fun trav tm =
        if is_comb tm then
           let val (M,N) = dest_comb tm
               val M' = trav M
               val N' = trav N
           in mk_comb (M',N') end
        else
        if is_abs tm then
          let val fvs = free_vars_lr tm
              val (bvars,M) = strip_abs tm
              val tm' = list_mk_abs(bvars,trav M)
              val fn_var_ty = list_mk_fun(map type_of fvs,type_of tm)
              val fn_var = new_defVar fn_var_ty
              val proto_left = list_mk_comb(fn_var,fvs)
              val proto_def = mk_eq(proto_left,tm')
              val fn_var_name = fst $ dest_var fn_var
              val def_name = fn_var_name ^"_def"
              val def = Definition.new_definition(def_name,proto_def)
              val left = lhs $ snd $ strip_forall $ concl def
          in
            def_list := def :: !def_list;
            left
          end
        else tm
      val new = trav (concl thm)
  in
    (!def_list |> rev, new)
  end

fun firstify thm =
  let val vs = fst $ strip_forall $ concl thm
      val th = SPEC_ALL thm
  in case find_defs th
      of ([],_) => NONE
       | (defs,tm) =>
       let val goal = mk_eq (concl thm, list_mk_forall(vs,tm))
           val eq_thm = prove(goal,simp defs)
           val defs' = map (SIMP_RULE bool_ss [FUN_EQ_THM]) defs
       in SOME (eq_thm, defs') end
  end

(* Following definition obviated by blunderbuss call to SIMP_RULE
   above, but possibly useful in a more tailored solution later on.

val unlambda_eq =
 let val fun_eq_imp = iffLR FUN_EQ_THM
 in fn th =>
    let val x = fst $ dest_abs $ rhs $ concl th
        val th1 = MATCH_MP fun_eq_imp th
    in RIGHT_BETA $ SPEC x th1
    end
 end
*)

end
