structure inline :> inline =
struct

open HolKernel Parse boolLib bossLib NormalTheory Normal
     pairLib pairSyntax PairRules basic;


(*---------------------------------------------------------------------------*)
(* Inline Expansion                                                          *)
(* Replace calls to small functions with their bodies                        *)
(*---------------------------------------------------------------------------*)

val threshold = ref 10;

fun size tm =
  if is_let tm then
     let val (v,M,N) = dest_plet tm
     in size M + size N end
  else if is_pabs tm then
     size (#2 (dest_pabs tm))
  else if is_cond tm then
     let val (J,M,N) = dest_cond tm
     in size M + size N + 1 end
  else if is_pair tm then
     let val (M,N) = dest_pair tm
     in size M + size N end
  else 1

(*---------------------------------------------------------------------------*)
(* Inline Expansion small anonymous functions defined in the body            *)
(*---------------------------------------------------------------------------*)

fun identify_small_fun tm =
  let
     fun trav t =
       if is_let t then
           let val (v,M,N) = dest_plet t
               val M' = if is_pabs M andalso size M < !threshold then
                           mk_comb (inst [alpha |-> type_of M] (Term `fun`), M)
                        else trav M
           in mk_plet (v, M', trav N)
           end
       else t
  in
    trav tm
  end;

fun once_expand_anonymous def =
  let
    val t0 = rhs (concl (SPEC_ALL def))
    val t1 = identify_small_fun t0
    val lem0 = REFL t1
    val lem1 = CONV_RULE (LHS_CONV (REWRITE_CONV [fun_ID])) lem0
    val thm1 = ONCE_REWRITE_RULE [lem1] def
    val thm2 = (PBETA_RULE o SIMP_RULE bool_ss [INLINE_EXPAND]) thm1
  in
    thm2
  end

fun expand_anonymous def =
  let
    fun expand th =
       let val th' =  once_expand_anonymous th
       in
         if concl th' = concl th then th'
         else expand th'
       end
       handle e => th   (* Unchanged *)
  in
    expand def
  end

(*---------------------------------------------------------------------------*)
(* Inline Expand small named functions                                       *)
(* Retrieve pre-defined functions stored in the environment                  *)
(*---------------------------------------------------------------------------*)

val unroll_limit = ref 3;

fun mk_inline_rules env =
  let fun unroll defth =
      let val (name,body) = dest_eq (concl defth)
      in  if occurs_in name body
            then PBETA_RULE  (* unroll the function *)
                  (CONV_RULE (RHS_CONV
                    (REWRITE_CONV
                       [Ntimes defth (!unroll_limit)])) defth)
            else
              defth
      end
  in
      List.map (unroll o abs_fun) env
  end

fun expand_named env def =
  let
    val rules = mk_inline_rules env
    val thm1 = (PBETA_RULE o ONCE_REWRITE_RULE rules) def (* inline expansion *)
  in
    thm1
  end


(*---------------------------------------------------------------------------*)
(* Optimization on Normal Forms:                                             *)
(*   1. SSA forms                                                            *)
(*   2. Inline expansion                                                     *)
(*   3. Simplification of let-expressions (atom_let, flatten_let, useless_let*)
(*   4. Constant folding                                                     *)
(*   5. Beta-reduction (a special case of constant folding)                  *)
(*---------------------------------------------------------------------------*)

fun optimize th =
  let val lem1 = SIMP_RULE arith_ss [] th              (* constant folding *)
      val lem2 = beta_reduction lem1                   (* beta_reduction *)
  in
      if concl lem2 = concl th then lem2
      else optimize lem2
  end

fun optimize_norm env def =
  let
    val th1 = SSA_RULE def
    val th2 = expand_anonymous th1
    val th3 = expand_named env th2
    val th4 = optimize th3
    val th5 = SIMP_RULE bool_ss [FLATTEN_LET] th4
    val th6 = beta_reduction th5
  in
    th6
  end

end (* struct *)
