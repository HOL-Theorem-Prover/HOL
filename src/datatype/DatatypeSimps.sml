(*---------------------------------------------------------------------------*
 * Simplifications for Datatypes. This Library extracts information about
 * datatypes from Typebase and provides some theorems and conversations that
 * are suitable to reason about this datatype.
 *---------------------------------------------------------------------------*)
structure DatatypeSimps :> DatatypeSimps =
struct

open HolKernel Parse boolLib TypeBasePure
open simpLib
val std_ss = boolSimps.bool_ss


fun map_option_filter f [] = []
  | map_option_filter f (x :: xs) = case (f x handle
      Interrupt => raise Interrupt | _ => NONE) of
        NONE => map_option_filter f xs
      | SOME fx => fx :: (map_option_filter f xs)

fun tyinfos_of_tys tyl = map_option_filter TypeBase.fetch tyl


(******************************************************************************)
(* Generating thms                                                            *)
(******************************************************************************)

fun make_variant_list n s avoid [] = []
  | make_variant_list n s avoid (h::t) =
      let val v = variant avoid (mk_var(s^Int.toString n, h))
      in v::make_variant_list (n + 1) s (v::avoid) t
      end

fun make_args_simple [] = []
  | make_args_simple (ty :: tys) = 
    let
      val arg0 = mk_var("M", ty);
      val args = make_variant_list 0 "f" [arg0] tys;
    in
      arg0 :: args
    end

fun make_args_abs tyL = let
  fun aux res n m avoid ty = let
    val (arg_tyL, base_ty) = strip_fun ty
    val args = make_variant_list m "x" avoid arg_tyL
    val b = variant (args @ avoid) (mk_var("f"^Int.toString n, ty))
  in
    ((args, b) :: res, n+1, m+(length arg_tyL), b::(args@avoid))
  end;
  val arg0 = mk_var("M", hd tyL);
  val (args, _, _, _) = foldl (fn (ty, (res, n, m, avoid)) =>
      aux res n m avoid ty) ([], 0, 0, [arg0]) (tl tyL)
in
  (arg0, rev args)
end

fun mk_type_forall_thm_tyinfo tyinfo = let
  val nchotomy_thm = nchotomy_of tyinfo;
  val ty = type_of (fst (dest_forall (concl nchotomy_thm)))

  val P_tm = mk_var ("P", ty --> bool)
  val input_tm = mk_var ("tt", ty)
  val body_tm = mk_comb (P_tm, input_tm)

  val thm_base = GSYM (CONJUNCT1 (SPEC body_tm IMP_CLAUSES))
  val true_expand_thm = GSYM (EQT_INTRO (SPEC input_tm nchotomy_thm))
  val thm1 = CONV_RULE (RHS_CONV (RATOR_CONV (RAND_CONV (K true_expand_thm)))) thm_base

  val thm2 = QUANT_CONV (K thm1) (mk_forall (input_tm, body_tm))
  val thm3 = CONV_RULE (RHS_CONV (SIMP_CONV std_ss [DISJ_IMP_THM, GSYM LEFT_FORALL_IMP_THM, FORALL_AND_THM])) thm2

  val thm4 = GEN P_tm thm3
in
  thm4
end


fun mk_type_quant_thms_tyinfo tyinfo = let
  val forall_thm = mk_type_forall_thm_tyinfo tyinfo;

  val (P_tm, _) = dest_forall (concl forall_thm)
  val P_arg_tm = genvar (hd (fst (strip_fun (type_of P_tm))))
  val P_neg_tm = mk_abs (P_arg_tm, mk_neg (mk_comb (P_tm, P_arg_tm)))

  val thm0 = SPEC P_neg_tm forall_thm
  val thm1 = AP_TERM boolSyntax.negation thm0 
  val thm3 = CONV_RULE (BINOP_CONV (SIMP_CONV std_ss [])) thm1
  val thm4 = GEN P_tm thm3
in
  (forall_thm, thm4)
end


fun mk_type_exists_thm_tyinfo tyinfo = 
  snd (mk_type_quant_thms_tyinfo tyinfo)


fun mk_case_elim_thm_tyinfo tyinfo = let
  val case_c = case_const_of tyinfo;
  val (arg_tyL, base_ty) = strip_fun (type_of case_c);
  val (input_arg, case_args) = make_args_abs arg_tyL
  val avoid = input_arg :: flatten (List.map (fn (args, b) => (b :: args)) case_args)
  val const = variant avoid (mk_var ("c", base_ty))

  val t0 = mk_comb (case_c, input_arg)
  val t1 = foldl (fn ((args, _), t) =>
     mk_comb (t, list_mk_abs (args, const))) t0 case_args
  val t2 = mk_eq (t1, const)
  val t3 = list_mk_forall ([input_arg, const], t2)

  val forall_thm = mk_type_forall_thm_tyinfo tyinfo
  val simp_thm = case_def_of tyinfo
  val thm0 = HO_REWR_CONV forall_thm t3
  val thm1 = CONV_RULE (RHS_CONV (REWRITE_CONV [simp_thm])) thm0
  val thm2 = EQT_ELIM thm1
in
  thm2
end


fun mk_type_rewrites_tyinfo tyinfo = let
  val thm_def0 = case_def_of tyinfo;
  val thms_def = CONJUNCTS thm_def0

  val thms_dist = case (distinct_of tyinfo) of
      NONE => []
    | SOME thm_dist0 => let 
        val thms_dist1 = CONJUNCTS thm_dist0
        val thms_dist = thms_dist1 @ List.map GSYM thms_dist1
      in thms_dist end

  val thms_one_one = case (one_one_of tyinfo) of
      NONE => []
    | SOME thm => CONJUNCTS thm;

  val elim_thms = [mk_case_elim_thm_tyinfo tyinfo]
in
  elim_thms @ thms_def @ thms_dist @ thms_one_one
end


fun mk_case_cong_thm_tyinfo tyinfo = let
  val case_c = case_const_of tyinfo;
  val (arg_tyL, base_ty) = strip_fun (type_of case_c);
  val (input_arg, case_args) = make_args_abs arg_tyL
  val avoid = input_arg :: flatten (List.map (fn (args, b) => (b :: args)) case_args)
  val input_arg' = variant avoid input_arg
  val (avoid, case_args') = Lib.foldl_map (fn (av, (args, v)) =>
      let val v' = variant av v in
      (v' :: av, (args, v')) end) (input_arg'::avoid, case_args)

  val case_args0 = List.map (fn (args, c) =>
     list_mk_abs (args, list_mk_comb (c, args)))
     case_args
  val t1a = list_mk_icomb (case_c, [input_arg] @ case_args0)

  val case_args1 = List.map (fn (args, c) =>
     list_mk_abs (args, list_mk_comb (c, args)))
     case_args'
  val t1b = list_mk_icomb (case_c, [input_arg'] @ case_args1)

  val t2 = mk_eq(t1a, t1b)

  val constr = constructors_of tyinfo
  val M_eq = mk_eq (input_arg, input_arg')
  fun mk_imp args c c' cr = let
     val t0 = list_mk_icomb (c, args) 
     val t1 = list_mk_icomb (c', args) 
     val t2 = mk_eq (t0, t1)
     val u0 = list_mk_icomb (cr, args)
     val u1 = mk_eq (input_arg', u0)
     val t3 = boolSyntax.mk_imp (u1, t2)
     val t4 = list_mk_forall (args, t3)
  in
    t4
  end
  val imps = List.map (fn (((args, c), (_, c')), cr) => 
     mk_imp args c c' cr)
     (zip (zip case_args case_args') constr)


  val t3 = boolSyntax.list_mk_imp  (M_eq::imps, t2) 
  val t4 = list_mk_forall ([input_arg, input_arg']@(List.map snd case_args)@(List.map snd case_args'), t3)

  val forall_thm = mk_type_forall_thm_tyinfo tyinfo
  val simp_thm = case_def_of tyinfo
  val thm0 = HO_REWR_CONV forall_thm t4
  val thm1 = CONV_RULE (RHS_CONV (SIMP_CONV std_ss [simp_thm])) thm0
  val thm2 = EQT_ELIM thm1
in
  thm2
end


fun mk_case_rand_thm_tyinfo tyinfo = let
  val case_c = case_const_of tyinfo;
  val (arg_tyL, base_ty) = strip_fun (type_of case_c);
  val (input_arg, case_args) = make_args_abs arg_tyL
  val avoid = input_arg :: flatten (List.map (fn (args, b) => (b :: args)) case_args)
  val res_ty = gen_tyvar ()
  val const = variant avoid (mk_var ("f", base_ty --> res_ty))

  val case_args0 = List.map (fn (args, c) =>
     list_mk_abs (args, list_mk_comb (c, args)))
     case_args
  val t1 = list_mk_icomb (case_c, [input_arg] @ case_args0)
  val t2a = mk_comb (const, t1)

  val case_args1 = List.map (fn (args, c) =>
     list_mk_abs (args, mk_comb (const, list_mk_comb (c, args)))) 
     case_args
  val t2b = list_mk_icomb (case_c, [input_arg] @ case_args1)

  val t3 = mk_eq (t2a, t2b)
  val consts = List.map snd case_args;
  val t4 = list_mk_forall ([input_arg, const]@consts, t3)

  val forall_thm = mk_type_forall_thm_tyinfo tyinfo
  val simp_thm = case_def_of tyinfo
  val thm0 = HO_REWR_CONV forall_thm t4
  val thm1 = CONV_RULE (RHS_CONV (SIMP_CONV std_ss [simp_thm])) thm0
  val thm2 = EQT_ELIM thm1
in
  thm2
end


fun mk_case_rator_thm_tyinfo tyinfo = let
  val case_c = case_const_of tyinfo;
  val (arg_tyL, base_ty) = strip_fun (type_of case_c);
  val res_ty = gen_tyvar ()
  val base_ty' = gen_tyvar ()
  val inst_ty = inst [base_ty |-> (res_ty --> base_ty')]

  val (input_arg, case_args) = make_args_abs arg_tyL
  val avoid = input_arg :: flatten (List.map (fn (args, b) => (b :: args)) case_args)
  val const = variant avoid (mk_var ("x", res_ty))

  val case_args0 = List.map (fn (args, c) =>
     list_mk_abs (args, list_mk_comb (c, args)))
     case_args
  val t1 = list_mk_icomb (case_c, [input_arg] @ case_args0)
  val t2 = inst_ty t1
  val t3a = mk_icomb (t2, const)

  val case_args1 = List.map (fn (args, c) =>
     list_mk_abs (args, mk_comb (inst_ty (list_mk_comb (c, args)), const))) 
     case_args
  val t3b = list_mk_icomb (case_c, [input_arg] @ case_args1)

  val t4 = mk_eq (t3a, t3b)
  val consts = List.map (fn (_, t) => inst_ty t) case_args;
  val t5 = list_mk_forall ([input_arg, const]@consts, t4)

  val forall_thm = mk_type_forall_thm_tyinfo tyinfo
  val simp_thm = case_def_of tyinfo
  val thm0 = HO_REWR_CONV forall_thm t5
  val thm1 = CONV_RULE (RHS_CONV (SIMP_CONV std_ss [simp_thm])) thm0
  val thm2 = EQT_ELIM thm1
in
  thm2
end


fun mk_case_abs_thm_tyinfo tyinfo = let
  val case_c = case_const_of tyinfo;
  val (arg_tyL, base_ty) = strip_fun (type_of case_c);
  val res_ty = gen_tyvar ()
  val base_ty' = gen_tyvar ()
  val inst_ty = inst [base_ty |-> (res_ty --> base_ty')]
  val (input_arg, case_args) = make_args_abs arg_tyL
  val avoid = input_arg :: flatten (List.map (fn (args, b) => (b :: args)) case_args)
  val const = variant avoid (mk_var ("x", res_ty))

  val case_args0 = List.map (fn (args, c) =>
     list_mk_abs (args, mk_comb (inst_ty (list_mk_comb (c, args)), const)))
     case_args
  val t1 = list_mk_icomb (case_c, [input_arg] @ case_args0)
  val t2a = mk_abs (const, t1)

  val case_args1 = List.map (fn (args, c) =>
     list_mk_abs (args, mk_abs (const, mk_comb (inst_ty (list_mk_comb (c, args)), const)))) 
     case_args
  val t2b = list_mk_icomb (case_c, [input_arg] @ case_args1)

  val t3 = mk_eq (t2a, t2b)
  val consts = List.map (fn (_, t) => inst [base_ty |-> (res_ty --> base_ty')] t) case_args;
  val t4 = list_mk_forall ([input_arg, const]@consts, t3)

  val forall_thm = mk_type_forall_thm_tyinfo tyinfo
  val simp_thm = case_def_of tyinfo
  val thm0 = HO_REWR_CONV forall_thm t4
  val thm1 = CONV_RULE (RHS_CONV (SIMP_CONV std_ss [simp_thm])) thm0
  val thm2 = EQT_ELIM thm1
in
  thm2
end


(******************************************************************************)
(* Lifting                                                                    *)
(******************************************************************************)

fun lift_case_const_CONV stop_consts rand_thms = let
  val conv = Ho_Rewrite.GEN_REWRITE_CONV I rand_thms
in (fn t => let 
  val thm = conv t 
  val (c, args) = strip_comb t 
in
  if (List.length args > 1 andalso List.exists (same_const c) stop_consts) then raise UNCHANGED else
  thm
end handle HOL_ERR _ => raise UNCHANGED) end 
  

fun lift_cases_typeinfos_ss til = let
   val rand_thms = Lib.mapfilter mk_case_rand_thm_tyinfo til
   val rator_thms = Lib.mapfilter mk_case_rator_thm_tyinfo til
   val abs_thms = Lib.mapfilter mk_case_abs_thm_tyinfo til
   val consts = Lib.mapfilter case_const_of til

   val conv_rand = lift_case_const_CONV consts rand_thms 
   val conv_rand_ss = simpLib.std_conv_ss {
      name = "lift_case_const_CONV",
      pats = [``f x``],
      conv = conv_rand}                                

   val rewr_ss = simpLib.rewrites (abs_thms @ rator_thms)
in
   simpLib.merge_ss [rewr_ss, conv_rand_ss]
end

fun lift_cases_ss tyL = lift_cases_typeinfos_ss (tyinfos_of_tys tyL)

fun lift_cases_stateful_ss () = lift_cases_typeinfos_ss (TypeBase.elts ())


(******************************************************************************)
(* Reverse Lifting                                                            *)
(******************************************************************************)

fun unlift_case_const_CONV stop_consts rand_thms = let
  val conv = Rewrite.GEN_REWRITE_CONV I empty_rewrites rand_thms
in (fn t => let 
  val thm = conv t 
  val (c, args) = strip_comb (rhs (concl thm))
in
  if (List.length args > 1 andalso List.exists (same_const c) stop_consts) then raise UNCHANGED else
  thm
end handle HOL_ERR _ => raise UNCHANGED) end 
  
fun unlift_cases_typeinfos_ss til = let
   val rand_thms = List.map GSYM (Lib.mapfilter mk_case_rand_thm_tyinfo til)
   val rator_thms = List.map GSYM (Lib.mapfilter mk_case_rator_thm_tyinfo til)
   val abs_thms = List.map GSYM (Lib.mapfilter mk_case_abs_thm_tyinfo til)
   val consts = Lib.mapfilter case_const_of til

   val conv_rand = unlift_case_const_CONV consts rand_thms 
   val conv_rand_ss = simpLib.std_conv_ss {
      name = "unlift_case_const_CONV",
      pats = [``f x``],
      conv = conv_rand}                                

   val conv_rator_ss = simpLib.std_conv_ss {
      name = "unlift_case_const_CONV",
      pats = [``f x``],
      conv = Rewrite.GEN_REWRITE_CONV I empty_rewrites rator_thms}                                

   val rewr_ss = simpLib.rewrites abs_thms
in
   simpLib.merge_ss [rewr_ss, conv_rator_ss, conv_rand_ss]
end

fun unlift_cases_ss tyL = unlift_cases_typeinfos_ss (tyinfos_of_tys tyL)

fun unlift_cases_stateful_ss () = unlift_cases_typeinfos_ss (TypeBase.elts ())


(******************************************************************************)
(* Simpset fragments                                                          *)
(******************************************************************************)

fun type_rewrites_typeinfos_ss til =
  rewrites (flatten (Lib.mapfilter mk_type_rewrites_tyinfo til))

fun type_rewrites_ss tyL = type_rewrites_typeinfos_ss (tyinfos_of_tys tyL)

fun type_rewrites_stateful_ss () = type_rewrites_typeinfos_ss (TypeBase.elts ())

fun congs thms = SSFRAG
    {name  = NONE,
     convs = [],
     rewrs = [],
        ac = [],
    filter = NONE,
    dprocs = [],
     congs = thms}

fun case_cong_typeinfos_ss til =
  simpLib.merge_ss [congs (Lib.mapfilter mk_case_cong_thm_tyinfo til),
		    type_rewrites_typeinfos_ss til]

fun case_cong_ss tyL = case_cong_typeinfos_ss (tyinfos_of_tys tyL)

fun case_cong_stateful_ss () = case_cong_typeinfos_ss (TypeBase.elts ())



fun expand_type_quants_typeinfos_ss til =
  rewrites (flatten (List.map (fn (x, y) => [x, y]) (Lib.mapfilter 
     mk_type_quant_thms_tyinfo til)))

fun expand_type_quants_ss tyL = expand_type_quants_typeinfos_ss (tyinfos_of_tys tyL)

fun expand_type_quants_stateful_ss () = expand_type_quants_typeinfos_ss (TypeBase.elts ())


(******************************************************************************)
(* Rule for eliminating case splits in equations                              *)
(******************************************************************************)

fun cases_to_top_RULE thm = let
  val input_thmL = BODY_CONJUNCTS thm
  val (input_eqL, input_restL) = partition (fn thm => is_eq (concl thm)) input_thmL 

  fun process_eq eq_thm = let
     val free_vars_lhs = free_vars (lhs (concl eq_thm));
     fun search_pred t = let
       val (c, args) = strip_comb t
       val _ = if length args = 0 then fail () else ();
       val _ = if (List.exists (term_eq (hd args)) free_vars_lhs) then () else fail();
       val case_const = TypeBase.case_const_of (type_of (hd args));
     in
       same_const c case_const
     end handle HOL_ERR _ => false;
     val case_term = find_term search_pred (rhs (concl eq_thm));
     val (_, split_args) = strip_comb case_term;
     val split_var = hd split_args;
     val tyinfo = valOf (TypeBase.fetch (type_of split_var)) handle Option => fail()
     val free_vars_full = free_vars (concl eq_thm)
     val split_terms = List.map (fn (c_tm, cr_tm) => let
        val (_, cr_ret_type) = strip_fun (type_of cr_tm);
        val ty_inst = match_type cr_ret_type (type_of split_var);
        val cr_tm' = inst ty_inst cr_tm;
        val (args, _) = strip_abs c_tm
        val (_, args') = foldl_map (fn (av, v) => let val v' = variant av v in (v' :: av, v') end) (free_vars_full, args)
      in list_mk_comb (cr_tm', args') end)
        (zip (tl split_args) (TypeBasePure.constructors_of tyinfo))


     val rhs_conv = REWRITE_CONV (#rewrs (TypeBasePure.simpls_of tyinfo)) THENC
                    DEPTH_CONV BETA_CONV
     fun process_thm split_tm = let
       val thm0 = INST [split_var |-> split_tm] eq_thm
       val thm1 = CONV_RULE (RHS_CONV rhs_conv) thm0
     in thm1 end
     val result = List.map process_thm split_terms
  in
    SOME result
  end handle HOL_ERR _ => NONE

  fun process_all acc [] = List.rev acc
    | process_all acc (eq_thm :: thms) = (case process_eq eq_thm of
          NONE => process_all (eq_thm :: acc) thms
        | SOME eq_thms => process_all acc (eq_thms @ thms))

  val processed_eq_thms = process_all [] input_eqL
  val all_thms = processed_eq_thms @ input_restL   
in
  LIST_CONJ (List.map GEN_ALL all_thms)
end

end
