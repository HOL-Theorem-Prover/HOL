structure tailrecLib :> tailrecLib =
struct

open HolKernel Parse boolLib simpLib boolSimps

val ERR = mk_HOL_ERR "tailrecLib"

type thmloc = DB_dtype.thm_src_location

val Cases = BasicProvers.Cases
val PairCases = pairLib.PairCases

(*----------------------------------------------------------------------*
    Miscellaneous helper functions
 *----------------------------------------------------------------------*)

fun list_mk_pair_case pat r =
  if not (pairSyntax.is_pair pat) then (pat,r) else let
    val v = genvar (type_of pat)
    val (x1,rest_pat) = pairSyntax.dest_pair pat
    val (y1,r1) = list_mk_pair_case rest_pat r
    val new_pat = pairSyntax.mk_pair(x1,y1)
    in (v,TypeBase.mk_case(v,[(new_pat,r1)])) end

fun auto_prove goal_tm (tac:tactic) = TAC_PROOF (([],goal_tm), tac)

(*----------------------------------------------------------------------*
    Function for proving that non-mutually recursive tail-recursive
    functions exist. The input function can only take one argument.
 *----------------------------------------------------------------------*)

val TAILREC_def = whileTheory.TAILREC
                  |> CONV_RULE (DEPTH_CONV ETA_CONV)
                  |> REWRITE_RULE [GSYM combinTheory.I_EQ_IDABS];

fun strip_to_dest test A t =
    if aconv test t then SOME A
    else
      case Lib.total dest_comb t of
          NONE => NONE
        | SOME (f,x) => strip_to_dest test (x::A) f

fun mk_sum_term fn_t inty tm =
    let
      fun build_sum t =
          if TypeBase.is_case t then
            let val (a,b,xs) = TypeBase.dest_case t
                val ys = map (apsnd build_sum) xs
            in
              TypeBase.mk_case (b,ys)
            end
          else if can pairSyntax.dest_anylet t then
            let val (xs,x) = pairSyntax.dest_anylet t
            in pairSyntax.mk_anylet(xs,build_sum x) end
          else if cvSyntax.is_cv_if t then
            let val (b,x,y) = cvSyntax.dest_cv_if t
            in mk_cond(cvSyntax.mk_c2b b,build_sum x,build_sum y) end
          else
            case strip_to_dest fn_t [] t of
                SOME xs => if null xs then
                             raise ERR "mk_sum_term" "malformed term"
                           else
                             sumSyntax.mk_inl
                               (pairSyntax.list_mk_pair xs, type_of t)
              | NONE =>
                if is_abs t then
                  mk_abs (apsnd build_sum (dest_abs t))
                else sumSyntax.mk_inr(t,inty)
    in
      build_sum tm
    end

fun prove_simple_tailrec_exists tm = let
  val (l,r) = dest_eq tm
  val (f_tm,arg_tm) = dest_comb l
  val arg_tms = if is_var arg_tm then [arg_tm] else free_vars arg_tm
  val goal_tm = mk_exists(f_tm,list_mk_forall(arg_tms,tm))
  val input_ty = type_of arg_tm
  val output_ty = type_of r
  fun mk_inl x = sumSyntax.mk_inl(x,output_ty)
  fun mk_inr x = sumSyntax.mk_inr(x,input_ty)
  (* building the witness *)
  val sum_tm = mk_sum_term f_tm input_ty r
  val _ = not (exists (aconv f_tm) (free_vars sum_tm)) orelse fail()
  val abs_sum_tm = pairSyntax.mk_pabs(arg_tm,sum_tm)
  val witness = ISPEC abs_sum_tm whileTheory.TAILREC |> SPEC_ALL
                |> concl |> dest_eq |> fst |> rator
  fun sum_case_exp tm = tm |> rator |> rator |> rand
  val sum_case_exp_conv = RATOR_CONV o RATOR_CONV o RAND_CONV
  (* tactic to solve goal *)
  fun tailrec_tac (assum_tms,goal_tm) =
    if (goal_tm |> dest_eq |> fst |> sum_case_exp |> sumSyntax.is_inr) then
      REWRITE_TAC [sumTheory.sum_case_def,combinTheory.I_THM]
        (assum_tms,goal_tm)
    else if (goal_tm |> dest_eq |> fst |> sum_case_exp |> sumSyntax.is_inl) then
      REWRITE_TAC [sumTheory.sum_case_def,combinTheory.I_THM]
        (assum_tms,goal_tm)
    else if cvSyntax.is_cv_if (rand goal_tm) then
      (CONV_TAC (RAND_CONV (REWR_CONV cvTheory.cv_if)) THEN tailrec_tac)
         (assum_tms,goal_tm)
    else if can pairSyntax.dest_anylet (goal_tm |> rand) then let
      val xs = pairSyntax.dest_anylet (goal_tm |> rand) |> fst
      val vs = xs |> map (fn (x,y) => (y,genvar (type_of y)))
      val specs = foldl (fn (x,t) => SPEC_TAC x THEN t) ALL_TAC vs
      val gens = foldr (fn ((_,x),t) =>
                    if can pairSyntax.dest_prod (type_of x) then
                      PairCases THEN t
                    else gen_tac THEN t) ALL_TAC vs
      fun expand_lets 0 = ALL_CONV
        | expand_lets 1 = (REWR_CONV LET_THM THENC PairRules.PBETA_CONV)
        | expand_lets n = ((RATOR_CONV o RAND_CONV) (expand_lets (n-1))
                           THENC expand_lets 1)
      val exp_conv = expand_lets (length vs)
      val exp_both_conv = RAND_CONV exp_conv THENC
                           (RATOR_CONV o RAND_CONV o sum_case_exp_conv) exp_conv
      in (specs THEN gens THEN CONV_TAC exp_both_conv)
           (assum_tms,goal_tm) end
    else if TypeBase.is_case (rand goal_tm) then let
      val (a,b,xs) = TypeBase.dest_case (rand goal_tm)
      val ty = type_of b
      val new_v = genvar ty
      val case_def = TypeBase.case_def_of ty
      in (SPEC_TAC (b,new_v) THEN Cases
          THEN PURE_ONCE_REWRITE_TAC [case_def]
          THEN CONV_TAC (DEPTH_CONV BETA_CONV))
            (assum_tms,goal_tm) end
    else NO_TAC (assum_tms,goal_tm);
  (* prove main theorem *)
  val tac = exists_tac witness
            THEN rpt gen_tac
            THEN CONV_TAC ((RATOR_CONV o RAND_CONV) (REWR_CONV TAILREC_def))
            THEN SPEC_TAC (witness, genvar (type_of witness))
            THEN gen_tac
            THEN PURE_REWRITE_TAC [boolTheory.literal_case_DEF]
            THEN CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
            THEN rpt (tailrec_tac \\ rpt conj_tac)
  val lemma = auto_prove goal_tm tac;
  in lemma end;

(*----------------------------------------------------------------------*
    Function for proving that mutually recursive tail-recursive
    functions exist. One equation per function. The arguments on the
    LHS of each equation must be variables.
 *----------------------------------------------------------------------*)

fun prove_tailrec_exists def_tm = let
  val defs = strip_conj def_tm
  (* build the goal to prove *)
  fun extract_def def_tm = let
    val (l,r) = dest_eq def_tm
    val (f_tm,args) = strip_comb l
    val _ = List.all is_var args orelse failwith "bad input"
    in (f_tm,list_mk_forall(args,def_tm)) end
  val xs = map extract_def defs
  val goal_tm = list_mk_exists(map fst xs, list_mk_conj(map snd xs))
  (* build one function *)
  val fs_args = map (strip_comb o fst o dest_eq) defs
  val tuples = map (fn (f,args) => pairSyntax.list_mk_pair args) fs_args
  val rhs_list = map (snd o dest_eq) defs
  fun build_sum_ty [] = fail()
    | build_sum_ty [(tm,r)] =
        if is_var tm then (type_of tm,[tm],tm,r) else let
          val (v,rhs_tm) = list_mk_pair_case tm r
          in (type_of tm,[tm],v,rhs_tm) end
    | build_sum_ty ((tm,r)::tms) = let
        val (ty1,calls1,v1,r1) = build_sum_ty [(tm,r)]
        val (ty2,calls2,v2,r2) = build_sum_ty tms
        val ty = sumSyntax.mk_sum(ty1,ty2)
        val v = genvar ty
        val pat1 = sumSyntax.mk_inl(v1,ty2)
        val pat2 = sumSyntax.mk_inr(v2,ty1)
        in (ty,
            map (fn x => sumSyntax.mk_inl(x,ty2)) calls1 @
            map (fn x => sumSyntax.mk_inr(x,ty1)) calls2,
            v,
            TypeBase.mk_case(v,[(pat1,r1),(pat2,r2)])) end
  val (input_ty, call_tms, arg_tm, rhs_tm) = build_sum_ty (zip tuples rhs_list)
  val output_ty = defs |> hd |> dest_eq |> snd |> type_of
  val combined_var_tm = mk_var("combined", input_ty --> output_ty)
  val lhs_tm = mk_comb(combined_var_tm, arg_tm)
  val calls =
    map2 (fn (f,args) => fn call_tm =>
          (f, list_mk_abs(args,mk_comb(combined_var_tm,call_tm))))
             fs_args call_tms
  val fixed_rhs_tm =
    rhs_tm |> subst (map (fn (x,y) => x |-> y) calls)
           |> QCONV (DEPTH_CONV BETA_CONV) |> concl |> rand
  val combined_eq = mk_eq(lhs_tm, fixed_rhs_tm)
  val combined_th = prove_simple_tailrec_exists combined_eq
  (* prove defining theorem *)
  val exists = foldr (fn (x,t) => EXISTS_TAC x THEN t) ALL_TAC (map snd calls)
  val tac =
    strip_assume_tac combined_th THEN exists
    THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN rpt conj_tac THEN rpt gen_tac
    THEN pop_assum (fn th => CONV_TAC ((RATOR_CONV o RAND_CONV) (REWR_CONV th)))
    THEN SIMP_TAC bool_ss [sumTheory.sum_case_def,pairTheory.pair_case_def]
  val lemma = auto_prove goal_tm tac
  in lemma end

(*----------------------------------------------------------------------*
    Defines tail-recursive functions based on the existance proofs
    that the above function can prove. Same restrictions apply.
 *----------------------------------------------------------------------*)

fun gen_tailrec_define {loc, name, def} =
    let
      val lemma = prove_tailrec_exists def
      val names = lemma |> concl |> strip_exists |> fst |> map (fst o dest_var)
    in
      boolSyntax.new_specification_at loc (name,names,lemma)
    end

fun tailrec_define name def =
    gen_tailrec_define {loc = Unknown, name = name, def = def}

end
