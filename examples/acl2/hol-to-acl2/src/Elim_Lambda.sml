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
(*                                                                           *)
(* 4. Prove equivalence of new term and old, using the new definitions.      *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

structure Elim_Lambda :> Elim_Lambda =
struct

open HolKernel boolLib bossLib

val ERR = mk_HOL_ERR "Elim_Lambda";

(*---------------------------------------------------------------------------*)
(* Stream of variables for auxiliary definitions                             *)
(*---------------------------------------------------------------------------*)

local
  val def_prefix = "Lam_"
  fun defName_of i = def_prefix^Int.toString i
  val num_stream = Portable.make_counter{init=0,inc=1}
in
fun new_defVar ty = mk_var(defName_of(num_stream()), ty)

fun is_defVar v =
   String.isPrefix def_prefix $ fst $ dest_var v
   handle HOL_ERR _ => false
end;

val def_list = ref [] : thm list ref

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
    else tm;

fun find_defs t =
  let val () = def_list := []
      val new = trav t
  in
    (!def_list |> rev, new)
  end

(*---------------------------------------------------------------------------*)
(* Stream of names for storing equivalence theorems under.                   *)
(*---------------------------------------------------------------------------*)

local
  val equiv_prefix = "Equiv_"
  val num_stream = Portable.make_counter{init=0,inc=1}
in
  fun equiv_thm_name() = equiv_prefix^Int.toString(num_stream())
end;

fun lift_lambdas tm =
  let val (vs,M) = strip_forall tm
  in case find_defs M
      of ([],_) => NONE
       | (defs,M') =>
       let val goal = mk_eq (tm, list_mk_forall(vs,M'))
           val eq_thm = prove(goal,simp defs)
           val _ = save_thm(equiv_thm_name(),eq_thm)
           val defs' = map (SIMP_RULE bool_ss [FUN_EQ_THM]) defs
       in SOME (eq_thm, defs') end
  end
  handle e as HOL_ERR _ =>
         raise wrap_exn "Elim_Lambda" "lift_lambdas" e;


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
