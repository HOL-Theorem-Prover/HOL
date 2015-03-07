structure deepMatchesLib :> deepMatchesLib =
struct

open HolKernel boolLib bossLib
open deepMatchesTheory
open simpLib
open quantHeuristicsLib
open DatatypeSimps
open deepMatchesSyntax
open Traverse
open constrFamiliesLib

(***********************************************)
(* Auxiliary stuff                             *)
(***********************************************)

fun make_gen_conv_ss c name ssl = let
   exception genconv_reducer_exn
   fun addcontext (context,thms) = context
   fun apply {solver,conv,context,stack,relation} tm = (
     QCHANGED_CONV (c (ssl, SOME (conv stack))) tm
   )
   in simpLib.dproc_ss (REDUCER {name=SOME name,
               addcontext=addcontext, apply=apply,
               initial=genconv_reducer_exn})
   end;


fun has_subterm p t = ((find_term p t; true) handle HOL_ERR _ => false)

(* We have a problem with conversions that loop in a fancy way.
   They add some pattern matching on the input variables and
   in the body the original term with renamed variables. The
   following function tries to detect this situation. *)
fun does_conv_loop thm = let
    val (l, r) = dest_eq (concl thm)
    fun my_mk_abs t = list_mk_abs (free_vars_lr t, t)
    val l' = my_mk_abs l
    val const_check = let
      val (l_c, _) = strip_comb l      
    in
      fn t => (same_const (fst (strip_comb t)) l_c)
    end handle HOL_ERR _ => (fn t => true)
    fun is_similar t = const_check t andalso (aconv l' (my_mk_abs t))
    val i = ((find_term is_similar r; true) handle HOL_ERR _ => false)
  in
    i
  end

(***********************************************)
(* Simpset to evaluate PMATCH_ROWS             *)
(***********************************************)

val PAIR_EQ_COLLAPSE = prove (
``(((FST x = (a:'a)) /\ (SND x = (b:'b))) = (x = (a, b)))``,
Cases_on `x` THEN SIMP_TAC std_ss [] THEN METIS_TAC[])

fun is_FST_eq x t = let
  val (l, r) = dest_eq t
  val pred = aconv (pairSyntax.mk_fst x)
in
  pred l
end

fun FST_SND_CONJUNCT_COLLAPSE v conj = let
  val conj'_thm = markerLib.move_conj_left (is_FST_eq v) conj

  val v' = pairSyntax.mk_snd v

  val thm_coll = (TRY_CONV (RAND_CONV (FST_SND_CONJUNCT_COLLAPSE v')) THENC
   (REWR_CONV PAIR_EQ_COLLAPSE))
    (rhs (concl conj'_thm))
in
  TRANS conj'_thm thm_coll
end handle HOL_ERR _ => raise UNCHANGED

fun ELIM_FST_SND_SELECT_CONV t = let
  val (v, conj) = boolSyntax.dest_select t
  val thm0 = FST_SND_CONJUNCT_COLLAPSE v conj

  val thm1 = RAND_CONV (ABS_CONV (K thm0)) t
  val thm2 = CONV_RULE (RHS_CONV (REWR_CONV SELECT_REFL)) thm1
in
  thm2
end handle HOL_ERR _ => raise UNCHANGED


(*
val rc = DEPTH_CONV pairTools.PABS_ELIM_CONV THENC SIMP_CONV list_ss [pairTheory.EXISTS_PROD, pairTheory.FORALL_PROD, PMATCH_ROW_EQ_NONE, PAIR_EQ_COLLAPSE, oneTheory.one]
*)

val pabs_elim_ss =
    simpLib.conv_ss
      {name  = "PABS_ELIM_CONV",
       trace = 2,
       key   = SOME ([],``UNCURRY (f:'a -> 'b -> bool)``),
       conv  = K (K pairTools.PABS_ELIM_CONV)}

val elim_fst_snd_select_ss =
    simpLib.conv_ss
      {name  = "ELIM_FST_SND_SELECT_CONV",
       trace = 2,
       key   = SOME ([],``$@ (f:'a -> bool)``),
       conv  = K (K ELIM_FST_SND_SELECT_CONV)}

val select_conj_ss =
    simpLib.conv_ss
      {name  = "SELECT_CONJ_SS_CONV",
       trace = 2,
       key   = SOME ([],``$@ (f:'a -> bool)``),
       conv  = K (K (SIMP_CONV (std_ss++boolSimps.CONJ_ss) []))};


val static_ss = simpLib.merge_ss
  [pabs_elim_ss,
   pairSimps.paired_forall_ss,
   pairSimps.paired_exists_ss,
   pairSimps.gen_beta_ss,
   select_conj_ss,
   elim_fst_snd_select_ss,
   boolSimps.EQUIV_EXTRACT_ss,
   simpLib.rewrites [
     some_var_bool_T, some_var_bool_F,
     GSYM boolTheory.F_DEF,
     pairTheory.EXISTS_PROD,
     pairTheory.FORALL_PROD,
     PMATCH_ROW_EQ_NONE,
     PMATCH_ROW_COND_def,
     PAIR_EQ_COLLAPSE,
     oneTheory.one]];

fun rc_ss gl = srw_ss() ++ simpLib.merge_ss (static_ss :: gl)

fun callback_CONV cb_opt t = (case cb_opt of
    NONE => NO_CONV t
  | SOME cb => cb t)

fun rc_conv (gl, callback_opt) = REPEATC (
  SIMP_CONV (rc_ss gl) [] THENC
  TRY_CONV (callback_CONV callback_opt))

fun rc_tac (gl, callback_opt) =
  CONV_TAC (rc_conv (gl, callback_opt))

fun PMATCH_ROW_ARGS_CONV c =
   RATOR_CONV (RAND_CONV (TRY_CONV c)) THENC
   RATOR_CONV (RATOR_CONV (RAND_CONV (TRY_CONV c))) THENC
   RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV (TRY_CONV c))))


(***********************************************)
(* converting between case-splits to PMATCH    *)
(***********************************************)

(*
val t = ``case x of
  (NONE, []) => 0`` *)

fun type_names ty =
  let val {Thy,Tyop,Args} = Type.dest_thy_type ty
  in {Thy=Thy,Tyop=Tyop}
  end;

(* destruct variant cases, see dest_case_fun *)
fun dest_case_fun_aux1 t = let
  val (f, args) = strip_comb t
  val (tys, _) = strip_fun (type_of f)
  val _ = if (List.null args) then failwith "dest_case_fun" else ()
  val ty = case tys of
      [] => failwith "dest_case_fun"
    | (ty::_) => ty
  val tn = type_names ty
  val ti = case TypeBase.fetch ty of
      NONE => failwith "dest_case_fun"
    | SOME ti => ti

  val _ = if (same_const (TypeBasePure.case_const_of ti) f) then
    () else  failwith "dest_case_fun"

  val ty_s = match_type (type_of (TypeBasePure.case_const_of ti)) (type_of f)
  val constrs = List.map (inst ty_s) (TypeBasePure.constructors_of ti)

  val a = hd args
  val ps = map2 (fn c => fn arg => let
    val (vars, res) = strip_abs arg in
    (list_mk_comb (c, vars), res) end) constrs (tl args)
in
  (a, ps)
end

(* destruct literal cases, see dest_case_fun *)
fun dest_case_fun_aux2 t = let
  val _ = if is_literal_case t then () else failwith "dest_case_fun"

  val (f, args) = strip_comb t

  val v = (el 2 args)
  val (v', b) = dest_abs (el 1 args)

  fun strip_cond acc b = let
    val (c, t_t, t_f) = dest_cond b
    val (c_l, c_r) = dest_eq c
    val _ = if (aconv c_l v') then () else failwith "dest_case_fun"
  in
    strip_cond ((c_r, t_t)::acc) t_f
  end handle HOL_ERR _ => (acc, b)

  val (ps_rev, c_else) = strip_cond [] b
  val ps = List.rev ((v', c_else) :: ps_rev)
in
  (v, ps)
end


(* destruct a case-function.
   The top-most split is split into the input + a list of rows.
   Each row consists of a pattern + the right-hand side. *)
fun dest_case_fun t = dest_case_fun_aux1 t handle HOL_ERR _ => dest_case_fun_aux2 t


fun case2pmatch_aux x t = let
  val (a, ps) = dest_case_fun t

  fun process_arg (p, rh) = let
    val x' = subst [a |-> p] x
  in
    (* recursive call *)
    case case2pmatch_aux x' rh of
        NONE => [(x', rh)]
      | SOME resl => resl
  end

  val ps = flatten (map process_arg ps)
in
  SOME ps
end handle HOL_ERR _ => NONE;

(* convert a case-term into a PMATCH-term, without any proofs *)
fun case2pmatch t = let
  val (f, args) = strip_comb t
  val _ = if (List.null args) then failwith "not a case-split" else ()

  val (p,patterns) = if is_literal_case t then (el 2 args, [el 1 args]) else
      (hd args, tl args)
  val v = genvar (type_of p)

  val t0 = if is_literal_case t then list_mk_comb (f, patterns @ [v]) else list_mk_comb (f, v::patterns)
  val ps = case case2pmatch_aux v t0 of
      NONE => failwith "not a case-split"
    | SOME ps => ps

  fun process_pattern (p, rh) = let
    val fvs = List.rev (free_vars p)
  in
    mk_PMATCH_ROW_PABS fvs (p, T, rh)
  end
  val rows = List.map process_pattern ps
  val rows_tm = listSyntax.mk_list (rows, type_of (hd rows))

  val rows_tm_p = subst [v |-> p] rows_tm
in
  mk_PMATCH p rows_tm_p
end

fun case_pmatch_eq_prove t t' = let
  val tm = mk_eq (t, t')

  (* very slow, simple approach. Just brute force.
     TODO: change implementation to get more runtime-speed *)
  val my_tac = (
    CASE_TAC THEN
    FULL_SIMP_TAC (rc_ss []) [PMATCH_EVAL, PMATCH_ROW_COND_def,
      PMATCH_INCOMPLETE_def]
  )
in
  (* set_goal ([], tm) *)
  prove (tm, REPEAT my_tac)
end handle HOL_ERR _ => raise UNCHANGED


fun PMATCH_INTRO_CONV t = 
  case_pmatch_eq_prove t (case2pmatch t)


(* convert a case-term into a PMATCH-term, without any proofs *)
fun pmatch2case t = let
  val (v, rows) = dest_PMATCH t 
  val fv = genvar (type_of v --> type_of t)

  fun process_row r = let
     val (vars_tm, pt, gt, rh) = dest_PMATCH_ROW_ABS r
     val _ = if (aconv gt T) then () else
       failwith ("guard present in row " ^
           (term_to_string r))

     val vars = FVL [vars_tm] empty_tmset
     val used_vars = FVL [pt] empty_tmset
     val free_vars = HOLset.difference (used_vars, vars)
     val _ = if (HOLset.isEmpty free_vars) then () else
       failwith ("free variables in pattern " ^ (term_to_string pt))
  in
     mk_eq (mk_comb (fv, pt), rh)
  end

  val row_eqs = map process_row rows
  val rows_tm = list_mk_conj row_eqs

  (* compile patterns with parse deep cases turned off *)
  val parse_pp = Feedback.current_trace "parse deep cases"
  val _ = Feedback.set_trace "parse deep cases" 0
  val case_tm0 = GrammarSpecials.compile_pattern_match rows_tm
  val _ = Feedback.set_trace "parse deep cases" parse_pp


  (* nearly there, now remove lambda's *)
  val (vs, case_tm1) = strip_abs case_tm0
  val case_tm = subst [el 2 vs |-> v] case_tm1
in
  case_tm
end

fun PMATCH_ELIM_CONV t = 
  case_pmatch_eq_prove t (pmatch2case t)


(***********************************************)
(* removing ARB rows                           *)
(***********************************************)

(* when converting CASE expressions into PMATCH,
   often ARB rows are introduced for the not
   covered cases. These ARB rows are
   not needed for PMATCH and can be removed. *)

(*
val rc_arg = []

set_trace "parse deep cases" 0
val t = convert_case ``case x of NONE => 0``

val t = convert_case ``case (x, y, z) of
   (0, y, z) => 2
 | (x, NONE, []) => x
 | (x, SOME y, l) => x+y``

*)

fun PMATCH_REMOVE_ARB_CONV_GENCALL_SINGLE rc_arg t = let
  val (v, rows) = dest_PMATCH t
  val rows_rev = List.rev rows

  val i_rev = index (fn row => (
    is_arb (#4(dest_PMATCH_ROW_ABS row)))
    handle HOL_ERR _ => false) rows_rev
  val i = length rows - (i_rev + 1)

  val rows1 = List.take (rows, i)
  val r = List.nth (rows, i)
  val rows2 = List.drop (rows, i+1)

  val r_ty = type_of r
  val rows1_tm = listSyntax.mk_list (rows1, r_ty)
  val rows2_tm = listSyntax.mk_list (rows2, r_ty)
  val r_thm = (snd (PMATCH_ROW_PABS_ELIM_CONV r)) handle
     UNCHANGED => REFL r

  val input_rows =
    listSyntax.mk_append (rows1_tm,
      listSyntax.mk_cons (rhs (concl r_thm), rows2_tm))

  val thm0 = PART_MATCH (rand o lhs o snd o dest_imp o #2 o strip_forall) (
    ISPEC v (FRESH_TY_VARS_RULE PMATCH_REMOVE_ARB_NO_OVERLAP)
  ) input_rows


  val pre = rand (rator (concl thm0))
  val pre_thm = prove (pre, rc_tac rc_arg)
  val thm1 = MP thm0 pre_thm
  val thm2 = CONV_RULE
    ((RHS_CONV o RAND_CONV) listLib.APPEND_CONV)
    thm1

  val thm2_lhs_tm = mk_eq (t, lhs (concl thm2))
  val thm2_lhs = prove (thm2_lhs_tm,
    MP_TAC r_thm THEN
    rc_tac rc_arg)

  val thm3 = TRANS thm2_lhs thm2
in
  thm3
end handle HOL_ERR _ => raise UNCHANGED

fun PMATCH_REMOVE_ARB_CONV_GENCALL rc_arg = REPEATC (PMATCH_REMOVE_ARB_CONV_GENCALL_SINGLE rc_arg)
fun PMATCH_REMOVE_ARB_CONV_GEN ssl = PMATCH_REMOVE_ARB_CONV_GENCALL (ssl, NONE)
val PMATCH_REMOVE_ARB_CONV = PMATCH_REMOVE_ARB_CONV_GEN []


(***********************************************)
(* Cleaning up unused vars in PMATCH_ROW       *)
(***********************************************)

(*val t = ``
PMATCH (SOME x, xz)
     [PMATCH_ROW (\x. (SOME 2,x,[])) (\x. T) (\x. x);
      PMATCH_ROW (\y:'a. ((SOME 2,3,[]))) (\y. T) (\y. x);
      PMATCH_ROW (\(z,x,yy). (z,x,[2])) (\(z,x,yy). T) (\(z,x,yy). x)]``
*)


(* Many simps depend on patterns being injective. This means
   in particular that no extra, unused vars occur in the patterns.
   The following removes such unused vars. *)

fun PMATCH_CLEANUP_PVARS_CONV t = let
  val _ = if is_PMATCH t then () else raise UNCHANGED

  fun row_conv row = let
     val (vars_tm, pt, gt, rh) = dest_PMATCH_ROW_ABS row
     val _ = if (type_of vars_tm = ``:unit``) then raise UNCHANGED else ()
     val vars = pairSyntax.strip_pair vars_tm
     val used_vars = FVL [pt, rh] empty_tmset

     val filtered_vars = filter (fn v => HOLset.member (used_vars, v)) vars

     val _ = if (length vars = length filtered_vars) then
       raise UNCHANGED else ()

     val row' = mk_PMATCH_ROW_PABS filtered_vars (pt, gt, rh)

     val eq_tm = mk_eq (row, row')
     (* set_goal ([], eq_tm) *)
     val eq_thm = prove (eq_tm,
        MATCH_MP_TAC PMATCH_ROW_EQ_AUX THEN
        rc_tac ([], NONE)
     )
  in
     eq_thm
  end
in
  CHANGED_CONV (DEPTH_CONV (PMATCH_ROW_FORCE_SAME_VARS_CONV THENC row_conv)) t
end handle HOL_ERR _ => raise UNCHANGED


(***********************************************)
(* Cleaning up by removing rows that           *)
(* don't match or are redundant                *)
(* also remove the whole PMATCH, if first      *)
(* row matches                                 *)
(***********************************************)

(*
val t = ``
PMATCH (NONE,x,l)
     [PMATCH_ROW (\x. (NONE,x,[])) (\x. T) (\x. x);
      PMATCH_ROW (\x. (NONE,x,[2])) (\x. F) (\x. x);
      PMATCH_ROW (\x. (NONE,x,[2])) (\x. T) (\x. x);
      PMATCH_ROW (\(x,y). (y,x,[2])) (\(x, y). T) (\(x, y). x);
      PMATCH_ROW (\x. (SOME 3,x,[])) (\x. T) (\x. x)
   ]``

val t = ``PMATCH y [PMATCH_ROW (\_0_1. _0_1) (\_0_1. T) (\_0_1. F)]``
val rc_arg = ([], NONE)

val t' = rhs (concl (PMATCH_CLEANUP_CONV t))
*)

fun map_filter f l = case l of
    [] => []
  | x::xs => (case f x of
       NONE => map_filter f xs
     | SOME y => y :: (map_filter f xs));

(* remove redundant rows *)
fun PMATCH_CLEANUP_CONV_GENCALL rc_arg t = let
  val (v, rows) = dest_PMATCH t

  fun check_row r = let
    val r_tm = mk_eq (mk_comb (r, v), optionSyntax.mk_none (type_of t))     val r_thm = rc_conv rc_arg r_tm
    val res_tm = rhs (concl r_thm)
  in
    if (same_const res_tm T) then SOME (true, r_thm) else
    (if (same_const res_tm F) then SOME (false, r_thm) else NONE)
  end handle HOL_ERR _ => NONE

  val (rows_checked_rev, _) = foldl (fn (r, (acc, abort)) =>
    if abort then ((r, NONE)::acc, true) else (
    let
      val res = check_row r
      val abort = (case res of
         (SOME (false, _)) => true
       | _ => false)
    in
      ((r, res)::acc, abort)
    end)) ([], false) rows
  val rows_checked = List.rev rows_checked_rev

  (* did we get any results? *)
  fun check_row_exists v rows =
     exists (fn x => case x of (_, SOME (v', _)) => v = v' | _ => false) rows

  val _ = if ((check_row_exists true rows_checked_rev) orelse (check_row_exists false rows_checked_rev)) then () else raise UNCHANGED

  val row_ty = type_of (hd rows)

  (* drop redundant rows *)
  val (thm0, rows_checked0) = let
    val n = index (fn x => case x of (_, SOME (false, _)) => true | _ => false) rows_checked
    val n_tm = numSyntax.term_of_int n

    val thma = ISPECL [v, listSyntax.mk_list (rows, row_ty), n_tm]
      (FRESH_TY_VARS_RULE PMATCH_ROWS_DROP_REDUNDANT_TRIVIAL_SOUNDNESS)

    val precond = fst (dest_imp (concl thma))
    val precond_thm = prove (precond,
      MP_TAC (snd(valOf (snd (el (n+1) rows_checked)))) THEN
      SIMP_TAC list_ss [quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE])

    val thmb = MP thma precond_thm

    val take_conv = RATOR_CONV (RAND_CONV reduceLib.SUC_CONV) THENC
                    listLib.FIRSTN_CONV
    val thmc = CONV_RULE (RHS_CONV (RAND_CONV take_conv)) thmb
  in
    (thmc, List.take (rows_checked, n+1))
  end handle HOL_ERR _ => (REFL t, rows_checked)

  (* drop false rows *)
  val (thm1, rows_checked1) = let
     val _ = if (exists (fn x => case x of (_, (SOME (true, _))) => true | _ => false) rows_checked0) then () else failwith "nothing to do"

     fun process_row ((r, r_thm_opt), thm) = (case r_thm_opt of
         (SOME (true, r_thm)) => let
           val thmA = PMATCH_EXTEND_OLD
           val thmB = HO_MATCH_MP thmA (EQT_ELIM r_thm)
           val thmC = HO_MATCH_MP thmB thm
        in
          thmC
        end
     | _ => let
           val thmA = PMATCH_EXTEND_BOTH_ID
           val thmB = HO_MATCH_MP thmA thm
        in
           ISPEC r thmB
        end)

    val base_thm = INST_TYPE [gamma |-> type_of t] (ISPECL [v, v] PMATCH_EXTEND_BASE)
    val thma = foldl process_row base_thm (List.rev rows_checked0)

    val rows_checked1 = filter (fn (_, res_opt) => case res_opt of
         SOME (true, thm) => false
     | _ => true) rows_checked0
  in
    (thma, rows_checked1)
  end handle HOL_ERR _ => (REFL (rhs (concl thm0)), rows_checked0)


  (* if first line matches, evaluate *)
  val thm2 = let
     val _ = if (not (List.null rows_checked1) andalso
                 (case hd rows_checked1 of (_, (SOME (false, _))) => true | _ => false)) then () else failwith "nothing to do"

     val thm1_tm = rhs (concl thm1)
     val thm2a = PART_MATCH (lhs o rand) PMATCH_EVAL_MATCH thm1_tm
     val pre_thm = EQF_ELIM (snd (valOf(snd (hd rows_checked1))))
     val thm2b = MP thm2a pre_thm

     val thm2c = CONV_RULE (RHS_CONV
        (RAND_CONV (rc_conv rc_arg) THENC
         pairLib.GEN_BETA_CONV)) thm2b handle HOL_ERR _ => thm2b
   in
     thm2c
   end handle HOL_ERR _ => let
     val _ = if (List.null rows_checked1) then () else failwith "nothing to do"
   in
     (REWR_CONV (CONJUNCT1 PMATCH_def)) (rhs (concl thm1))
   end handle HOL_ERR _ => REFL (rhs (concl thm1))
in
  TRANS (TRANS thm0 thm1) thm2
end handle HOL_ERR _ => raise UNCHANGED


fun PMATCH_CLEANUP_CONV_GEN ssl = PMATCH_CLEANUP_CONV_GENCALL (ssl, NONE)
val PMATCH_CLEANUP_CONV = PMATCH_CLEANUP_CONV_GEN [];



(***********************************************)
(* simplify a column                           *)
(***********************************************)

fun pair_get_col col v = let
  val vs = pairSyntax.strip_pair v
  val c_v = List.nth (vs, col)
  val vs' = List.take (vs, col) @
            List.drop (vs, col+1)
  val _ = if (List.null vs') then failwith "pair_get_col"
      else ()
  val v' = pairSyntax.list_mk_pair vs'
in
  (v', c_v)
end;

(*----------------*)
(* drop a column  *)
(*----------------*)

(*
val t = ``
PMATCH (NONE,x,l)
     [PMATCH_ROW (\x. (NONE,x,[])) (\x. T) (\x. x);
      PMATCH_ROW (\z. (NONE,z,[2])) (\z. F) (\z. z);
      PMATCH_ROW (\x. (NONE,x,[2])) (\x. T) (\x. x);
      PMATCH_ROW (\(z,y). (y,z,[2])) (\(z, y). IS_SOME y) (\(z, y). y)
   ]``


val t = ``
  PMATCH (x + y,ys)
    [PMATCH_ROW (λx. (x,[])) (λx. T) (λx. x);
     PMATCH_ROW (λ(x,y,ys). (x,y::ys)) (λ(x,y,ys). T)
       (λ(x,y,ys). my_d (x + y,ys))]``


val t = ``PMATCH (x,y)
    [PMATCH_ROW (λx. (x,x)) (λx. T) (λx. T);
     PMATCH_ROW (λ (z, y). (z, y)) (λ (z, y). T) (λ (z, y). F)]``


val rc_arg = []
val col = 0
*)

fun PMATCH_REMOVE_COL_AUX rc_arg col t = let
  val (v, rows) = dest_PMATCH t
  val (v', c_v) = pair_get_col col v
  val vs = free_vars c_v

  fun PMATCH_ROW_REMOVE_FUN_VAR_COL_AUX row = let
     val (vars_tm, pt, gt, rh) = dest_PMATCH_ROW_ABS_VARIANT vs row
     val vars = pairSyntax.strip_pair vars_tm
     val avoid = free_varsl [pt, gt, rh]

     val (pt0', pv) = pair_get_col col pt
     val pt' = subst [pv |-> c_v] pt0'

     val pv_i_opt = SOME (index (aconv pv) vars) handle HOL_ERR _ => NONE
     val (vars'_tm, f) = case pv_i_opt of
         (SOME pv_i) => (let
           (* we eliminate a variabe column *)
           val vars' = let
             val vars' = List.take (vars, pv_i) @ List.drop (vars, pv_i+1)
           in
             if (List.null vars') then [variant avoid ``uv:unit``] else vars'
           end

           val vars'_tm = pairSyntax.list_mk_pair vars'
           val g' = let
             val vs = List.take (vars, pv_i) @ (c_v :: List.drop (vars, pv_i+1))
             val vs_tm = pairSyntax.list_mk_pair vs
           in
             pairSyntax.mk_pabs (vars'_tm, vs_tm)
           end
         in
           (vars'_tm, g')
         end)
       | NONE => (let
           (* we eliminate a costant columns *)
           val (sub, _) = match_term pv c_v
           val _ = if List.all (fn x => List.exists (aconv (#redex x)) vars) sub then () else failwith "not a constant-col after all"

           val vars' = filter (fn v => not (List.exists (fn x => (aconv v (#redex x))) sub)) vars
           val vars' = if (List.null vars') then [genvar ``:unit``] else vars'
           val vars'_tm = pairSyntax.list_mk_pair vars'

           val g' = pairSyntax.mk_pabs (vars'_tm, Term.subst sub vars_tm)
         in
           (vars'_tm, g')
         end)

(*   val f = pairSyntax.mk_pabs (vars_tm, pt)
     val f' = pairSyntax.mk_pabs (vars'_tm, pt')
     val g = pairSyntax.mk_pabs (vars_tm, rh)

*)
     val p = pairSyntax.mk_pabs (vars_tm, pt)
     val p' = pairSyntax.mk_pabs (vars'_tm, pt')
     val g = pairSyntax.mk_pabs (vars_tm, gt)
     val r = pairSyntax.mk_pabs (vars_tm, rh)

     val thm0 = let
       val thm = FRESH_TY_VARS_RULE PMATCH_ROW_REMOVE_FUN_VAR
       val thm = ISPEC v thm
       val thm = ISPEC v' thm
       val thm = ISPEC f thm
       val thm = ISPEC p thm
       val thm = ISPEC g thm
       val thm = ISPEC r thm
       val thm = ISPEC p' thm

       fun elim_conv_aux vs = (
         (pairTools.PABS_INTRO_CONV vs) THENC
         (DEPTH_CONV (pairLib.PAIRED_BETA_CONV ORELSEC BETA_CONV))
       )

       fun elim_conv vs = PMATCH_ROW_ARGS_CONV (elim_conv_aux vs)
       val thm = CONV_RULE ((RAND_CONV o RHS_CONV) (elim_conv vars'_tm)) thm

       val tm_eq = mk_eq(lhs (rand (concl thm)), mk_comb (row, v))
       val eq_thm = prove (tm_eq, rc_tac rc_arg)

       val thm = CONV_RULE (RAND_CONV (LHS_CONV (K eq_thm))) thm
     in
       thm
     end

     val pre_tm = fst (dest_imp (concl thm0))
(* set_goal ([], pre_tm) *)
     val pre_thm = prove (pre_tm, rc_tac rc_arg)
     val thm1 = MP thm0 pre_thm
  in
     thm1
  end

  fun process_row (row, thm) = let
    val row_thm = PMATCH_ROW_REMOVE_FUN_VAR_COL_AUX row
    val thmA = PMATCH_EXTEND_BOTH
    val thmB = HO_MATCH_MP thmA row_thm
    val thmC = HO_MATCH_MP thmB thm
  in
    thmC
  end

  val base_thm = INST_TYPE [gamma |-> type_of t] (ISPECL [v, v'] PMATCH_EXTEND_BASE)
  val thm0 = List.foldl process_row base_thm (List.rev rows)
in
  thm0
end handle HOL_ERR _ => raise UNCHANGED


(*------------------------------------*)
(* remove a constructor from a column *)
(*------------------------------------*)

(*
val t = ``
PMATCH (SOME y,x,l)
     [PMATCH_ROW (\x. (SOME 0,x,[])) (\x. T) (\x. x);
      PMATCH_ROW (\z. (SOME 1,z,[2])) (\z. F) (\z. z);
      PMATCH_ROW (\x. (SOME 3,x,[2])) (\x. T) (\x. x);
      PMATCH_ROW (\(z,y). (y,z,[2])) (\(z, y). IS_SOME y) (\(z, y). y)
   ]``

val rc_arg = []
val col = 0
*)


fun PMATCH_REMOVE_FUN_AUX rc_arg col t = let
  val (v, rows) = dest_PMATCH t

  val (ff_tm, ff_inv, ff_inv_var, c) = let
    val vs = pairSyntax.strip_pair v
    val c_args = List.nth(vs, col)
    val (c, args) = strip_comb c_args

    val vs_vars = List.map (fn t => genvar (type_of t)) vs
    val args_vars = List.map (fn t => genvar (type_of t)) args

    val vars = List.take (vs_vars, col) @ args_vars @
               List.drop (vs_vars, col+1)
    val ff_res = List.take (vs_vars, col) @ list_mk_comb (c, args_vars) :: List.drop (vs_vars, col+1)
    val ff_tm = pairSyntax.mk_pabs (pairSyntax.list_mk_pair vars,
       pairSyntax.list_mk_pair ff_res)

    fun ff_inv tt = let
      val tts = pairSyntax.strip_pair tt
      val tt_args = List.nth(tts, col)

      val (c', args') = strip_comb tt_args
      val _ = if (aconv c c') then () else failwith "different constr"

      val vars = List.take (tts, col) @ args' @
                 List.drop (tts, col+1)
    in
      pairSyntax.list_mk_pair vars
    end

    fun ff_inv_var avoid tt = let
      val tts = pairSyntax.strip_pair tt
      val tt_col = List.nth(tts, col)

      val _ = if (is_var tt_col) then () else failwith "no var"

      val (var_basename, _) = dest_var (tt_col)
      fun gen_var i arg = let
        val n = var_basename ^ "_"^int_to_string i
      in
        mk_var (n, type_of arg)
      end


      val (args, _) = quantHeuristicsTools.list_variant avoid (mapi gen_var args_vars)

      val vars = List.take (tts, col) @ args @
                 List.drop (tts, col+1)
    in
      (pairSyntax.list_mk_pair vars, tt_col, args)
    end

  in
    (ff_tm, ff_inv, ff_inv_var, c)
  end

  val ff_thm_tm = ``!x y. (^ff_tm x = ^ff_tm y) ==> (x = y)``
  val ff_thm = prove (ff_thm_tm, rc_tac rc_arg)

  val v' = ff_inv v

  val PMATCH_ROW_REMOVE_FUN' = let
    val thm0 =  FRESH_TY_VARS_RULE PMATCH_ROW_REMOVE_FUN
    val thm1 = ISPEC ff_tm  thm0
    val thm2 = ISPEC v'  thm1
    val thm3 = MATCH_MP thm2 ff_thm

    val thm_v' = prove (``^ff_tm ^v' = ^v``, rc_tac rc_arg)
    val thm4 = CONV_RULE (STRIP_QUANT_CONV (LHS_CONV (RAND_CONV (K thm_v')))) thm3
  in
    thm4
  end

  fun PMATCH_ROW_REMOVE_FUN_COL_AUX row = let
     val (vars_tm, pt, gt, rh) = dest_PMATCH_ROW_ABS row

     val pt' = ff_inv pt
     val vpt' = pairSyntax.mk_pabs (vars_tm, pt')
     val vgt = pairSyntax.mk_pabs (vars_tm, gt)
     val vrh = pairSyntax.mk_pabs (vars_tm, rh)

     val thm0 = ISPECL [vpt', vgt, vrh] PMATCH_ROW_REMOVE_FUN'
     val eq_thm_tm = mk_eq (lhs (concl thm0), mk_comb (row, v))
     val eq_thm = prove (eq_thm_tm, rc_tac rc_arg)

     val thm1 = CONV_RULE (LHS_CONV (K eq_thm)) thm0

     val vi_conv = (pairTools.PABS_INTRO_CONV vars_tm) THENC
         (DEPTH_CONV (pairLib.PAIRED_BETA_CONV ORELSEC BETA_CONV))

     val thm2 = CONV_RULE (RHS_CONV (PMATCH_ROW_ARGS_CONV vi_conv)) thm1
  in
     thm2
  end

  fun PMATCH_ROW_REMOVE_VAR_COL_AUX row = let
     val (vars_tm, pt, gt, rh) = dest_PMATCH_ROW_ABS row
     val vars = pairSyntax.strip_pair vars_tm

     val avoid = vars @ free_vars pt @ free_vars rh @ free_vars gt
     val (pt', pv, new_vars) = ff_inv_var avoid pt

     val pv_i = index (aconv pv) vars

     val vars' = let
       val vars' = List.take (vars, pv_i) @ new_vars @ List.drop (vars, pv_i+1)
     in
       if (List.null vars') then [variant avoid ``uv:unit``] else vars'
     end

     val vars'_tm = pairSyntax.list_mk_pair vars'
     val f_tm = let
        val c_v = list_mk_comb (c, new_vars)
        val vs = List.take (vars, pv_i) @ (c_v :: List.drop (vars, pv_i+1))
        val vs_tm = pairSyntax.list_mk_pair vs
     in
        pairSyntax.mk_pabs (vars'_tm, vs_tm)
     end

     val vpt = pairSyntax.mk_pabs (vars_tm, pt)
     val vpt' = pairSyntax.mk_pabs (vars'_tm, pt')
     val vrh = pairSyntax.mk_pabs (vars_tm, rh)
     val vgt = pairSyntax.mk_pabs (vars_tm, gt)

     val thm0 = let
       val thm = FRESH_TY_VARS_RULE PMATCH_ROW_REMOVE_FUN_VAR
       val thm = ISPEC v thm
       val thm = ISPEC v' thm
       val thm = ISPEC f_tm thm
       val thm = ISPEC vpt thm
       val thm = ISPEC vgt thm
       val thm = ISPEC vrh thm
       val thm = ISPEC vpt' thm

       fun elim_conv vs = PMATCH_ROW_ARGS_CONV (
         (pairTools.PABS_INTRO_CONV vs) THENC
         (DEPTH_CONV (pairLib.PAIRED_BETA_CONV ORELSEC BETA_CONV))
       )

       val thm = CONV_RULE ((RAND_CONV o RHS_CONV) (elim_conv vars'_tm)) thm

       val tm_eq = mk_eq(lhs (rand (concl thm)), mk_comb (row, v))
       val eq_thm = prove (tm_eq, rc_tac rc_arg)

       val thm = CONV_RULE (RAND_CONV (LHS_CONV (K eq_thm))) thm
     in
       thm
     end

     val pre_tm = fst (dest_imp (concl thm0))
     val pre_thm = prove (pre_tm, rc_tac rc_arg)

     val thm1 = MP thm0 pre_thm
  in
     thm1
  end


  fun process_row (row, thm) = let
    val row_thm = PMATCH_ROW_REMOVE_FUN_COL_AUX row handle HOL_ERR _ =>
                  PMATCH_ROW_REMOVE_VAR_COL_AUX row
    val thmA = PMATCH_EXTEND_BOTH
    val thmB = HO_MATCH_MP thmA row_thm
    val thmC = HO_MATCH_MP thmB thm
  in
    thmC
  end

(*
  val row = el 1 (List.rev rows)
  val thm = base_thm
  val thm = thm0
*)

  val base_thm = INST_TYPE [gamma |-> type_of t] (ISPECL [v, v'] PMATCH_EXTEND_BASE)
  val thm0 = foldl process_row base_thm (List.rev rows)
in
  thm0
end handle HOL_ERR _ => raise UNCHANGED


(*------------------------*)
(* Combine auxiliary funs *)
(*------------------------*)

(*
val t = ``
PMATCH (SOME y,x,l)
     [PMATCH_ROW (\x. (SOME 0,x,[])) (\x. T) (\x. x);
      PMATCH_ROW (\z. z) (\z. F) (\z. (FST (SND z)));
      PMATCH_ROW (\x. (SOME 3,x)) (\x. T) (\x. (FST x));
      PMATCH_ROW (\(z,y). (y,z,[2])) (\(z, y). IS_SOME y) (\(z, y). y)
   ]``
val rc_arg = []
*)

fun PMATCH_SIMP_COLS_CONV_GENCALL rc_arg t = let
  val cols = dest_PMATCH_COLS t
(*
  val (col_v, col) = el 1 cols
  val (vars, col_pat) = el 3  col
*)
  fun do_match col_v (vars, col_pat) = let
    val (sub, _) = match_term col_pat col_v
    val vars_ok = List.all (fn x => (List.exists (aconv (#redex x)) vars)) sub
  in
    vars_ok
  end handle HOL_ERR _ => false

  fun elim_col_ok (col_v, col) =
    List.all (do_match col_v) col

  fun simp_col_ok (col_v, col) = let
    val (c, args) = strip_comb col_v
    val _ = if (List.null args) then failwith "elim_col instead" else ()

    fun check_line (vars, pt) =
      (List.exists (aconv pt) vars) orelse
      (aconv (fst (strip_comb pt)) c)
  in
    List.all check_line col
  end handle HOL_ERR _ => false

  fun process_col i col = if (elim_col_ok col) then
    SOME (PMATCH_REMOVE_COL_AUX rc_arg i t)
  else if (simp_col_ok col) then
    SOME (PMATCH_REMOVE_FUN_AUX rc_arg i t)
  else NONE

  val thm_opt = first_opt process_col cols
in
  case thm_opt of NONE => raise UNCHANGED
                | SOME thm => thm
end

fun PMATCH_SIMP_COLS_CONV_GEN ssl = PMATCH_SIMP_COLS_CONV_GENCALL (ssl, NONE)
val PMATCH_SIMP_COLS_CONV = PMATCH_SIMP_COLS_CONV_GEN []


(***********************************************)
(* Expand columns                              *)
(***********************************************)

(* Sometimes not all rows of a PMATCH have the same number of
   explicit columns. This can happen, if some patterns are
   explicit pairs, while others are not. The following tries
   to expand columns into explicit ones. *)

(*
val t = ``
PMATCH (SOME y,x,l)
     [PMATCH_ROW (\x. (SOME 0,x,[])) (\x. T) (\x. x);
      PMATCH_ROW (\z. z) (\z. F) (\z. (FST (SND z)));
      PMATCH_ROW (\x. (SOME 3,x)) (\x. T) (\x. (FST x));
      PMATCH_ROW (\(z,y). (y,z,[2])) (\(z, y). IS_SOME y) (\(z, y). y)
   ]``
*)


fun PMATCH_EXPAND_COLS_CONV t = let
  val (v, rows) = dest_PMATCH t

  val col_no_v = length (pairSyntax.strip_pair v)
  val col_no = foldl (fn (r, m) => let
    val (_, pt, _) = dest_PMATCH_ROW r
    val m' = length (pairSyntax.strip_pair pt)
    val m'' = if m' > m then m' else m
  in m'' end) col_no_v rows

  fun split_var avoid cols l = let
    fun splits acc no ty = if (no = 0) then List.rev (ty::acc) else
    let
      val (ty_s, ty') = pairSyntax.dest_prod ty
    in
      splits (ty_s::acc) (no - 1) ty'
    end

    val types = splits [] (col_no - cols) (type_of l)

    val var_basename = fst (dest_var l) handle HOL_ERR _ => "v"
    fun gen_var i ty = let
       val n = var_basename ^ "_"^int_to_string i
    in
      mk_var (n, ty)
    end

    val (new_vars, _) = quantHeuristicsTools.list_variant avoid (mapi gen_var types)
  in
    new_vars
  end

  fun PMATCH_ROW_EXPAND_COLS row = let
     val (vars_tm, pt, gt, rh) = dest_PMATCH_ROW_ABS row

     val vars = pairSyntax.strip_pair vars_tm
     val pts = pairSyntax.strip_pair pt
     val cols = length pts

     val _ = if (cols < col_no) then () else failwith "nothing to do"
     val l = last pts

     val _ = if (List.exists (aconv l) vars) then () else failwith "nothing to do"

     val avoids = vars @ free_vars pt @ free_vars gt @ free_vars rh
     val new_vars = split_var avoids cols l

     val sub = [l |-> pairSyntax.list_mk_pair new_vars]
     val pt' = Term.subst sub pt
     val gt' = Term.subst sub gt
     val rh' = Term.subst sub rh
     val vars' = pairSyntax.strip_pair (Term.subst sub vars_tm)

     val row' = mk_PMATCH_ROW_PABS vars' (pt', gt', rh')

     val eq_tm = mk_eq(row, row')
     val eq_thm = prove (eq_tm, rc_tac ([], NONE))
     val thm = AP_THM eq_thm v
  in
     thm
  end handle HOL_ERR _ => REFL (mk_comb (row, v))

  fun process_row (row, thm) = let
    val row_thm = PMATCH_ROW_EXPAND_COLS row
    val thmA = PMATCH_EXTEND_BOTH
    val thmB = HO_MATCH_MP thmA row_thm
    val thmC = HO_MATCH_MP thmB thm
  in
    thmC
  end

  val base_thm = INST_TYPE [gamma |-> type_of t] (ISPECL [v, v] PMATCH_EXTEND_BASE)
  val thm0 = foldl process_row base_thm (List.rev rows)

  val thm1 = if (col_no_v >= col_no) then thm0 else let
     val avoids = free_vars t
     val vs = pairSyntax.strip_pair v
     val l = List.last vs
     val new_vars = split_var avoids col_no_v l
     val new_vars_tm = pairSyntax.list_mk_pair new_vars

     val sub = [l |-> new_vars_tm]

     val tt = rhs (concl thm0)
     val tt' = Term.subst sub tt
     val tt'' = boolSyntax.mk_let (pairSyntax.mk_pabs (new_vars_tm, tt'), l)

     val thm_eq = prove (mk_eq (tt, tt''),
       SIMP_TAC (rc_ss []) [LET_DEF])
  in
     TRANS thm0 thm_eq
  end
in
  thm1
end handle HOL_ERR _ => raise UNCHANGED;


(***********************************************)
(* PMATCH_SIMP_CONV                            *)
(***********************************************)

(*
val t = ``
PMATCH (SOME y,x,l)
     [PMATCH_ROW (\x. (SOME 0,x,[])) (\y. T) (\x. x);
      PMATCH_ROW (\z. z) (\z. F) (\z. (FST (SND z)));
      PMATCH_ROW (\x. (SOME 3,x)) (\x. T) (\x. (FST x));
      PMATCH_ROW (\(z,y). (y,z,[2])) (\(z, y). IS_SOME y) (\(z, y). y)
   ]``
*)

fun PMATCH_SIMP_CONV_GENCALL_AUX rc_arg = 
REPEATC (FIRST_CONV [
  CHANGED_CONV (PMATCH_CLEANUP_PVARS_CONV),
  CHANGED_CONV (PMATCH_CLEANUP_CONV_GENCALL rc_arg),
  CHANGED_CONV (PMATCH_REMOVE_ARB_CONV_GENCALL rc_arg),
  CHANGED_CONV (PMATCH_SIMP_COLS_CONV_GENCALL rc_arg),
  CHANGED_CONV (PMATCH_EXPAND_COLS_CONV),
  CHANGED_CONV PMATCH_FORCE_SAME_VARS_CONV
]);

fun PMATCH_SIMP_CONV_GENCALL rc_arg t = 
  if (is_PMATCH t) then PMATCH_SIMP_CONV_GENCALL_AUX rc_arg t else 
  raise UNCHANGED

fun PMATCH_SIMP_CONV_GEN ssl = PMATCH_SIMP_CONV_GENCALL (ssl, NONE)

val PMATCH_SIMP_CONV = PMATCH_SIMP_CONV_GEN [];

fun PMATCH_SIMP_GEN_ss ssl = 
  make_gen_conv_ss PMATCH_SIMP_CONV_GENCALL "PMATCH_SIMP_REDUCER" ssl

val PMATCH_SIMP_ss = PMATCH_SIMP_GEN_ss []


(***********************************************)
(* Lifting to lowest boolean level             *)
(***********************************************)

(* 



val tm = ``P (
  CASE xx OF [
    ]):bool``

val tm = ``P (
  CASE xx OF [
    || (x, y, ys). (x, y::ys) ~> (x + y);
    ||.  (0, []) ~> 9;
    || x.  (x, []) when x > 3 ~> x;
    || x.  (x, []) ~> 0]):bool``

val tm = mk_comb (P_v, p_tm)
val rc_arg = ([], NONE)
*)

fun PMATCH_LIFT_BOOL_CONV_AUX rc_arg tm = let
  val (p_tm, m_tm) = dest_comb tm
  val (v, rows) = dest_PMATCH m_tm
in
  case rows of
     [] =>
     REWRITE_CONV [PMATCH_PRED_UNROLL_NIL] tm
   | row::rows' => let
(*    val (row::rows') = rows *)
      val (pt, gt, rh) = dest_PMATCH_ROW row
      val rows'_tm = listSyntax.mk_list (rows', type_of row)

      (* instantiate base thm and try to prove precond *)
      val (thm1, is_inj) = let
        val thm00 = FRESH_TY_VARS_RULE PMATCH_PRED_UNROLL_CONS
        val thm01 = ISPECL [p_tm, v, pt, gt, rh, rows'_tm] thm00
        val pre = fst (dest_imp (concl thm01))
        val pre_thm = Lib.with_flag (Feedback.emit_MESG, false) prove (pre, rc_tac rc_arg)
      in
        (MP thm01 pre_thm, true)
      end handle HOL_ERR _ => let
         (* proving precond failed, try fallback theorem *)
        val thm00 = FRESH_TY_VARS_RULE PMATCH_PRED_UNROLL_CONS_NO_INJ
        val thm01 = ISPECL [p_tm, v, pt, gt, rh, rows'_tm] thm00
      in
        (thm01, false)
      end

      (* Use right variable names *)
      val thm2 = let
        val vars_tm = fst (pairSyntax.dest_pabs pt)

        val c = (RAND_CONV (pairTools.PABS_INTRO_CONV vars_tm)) THENC
                TRY_CONV (pairTools.ELIM_TUPLED_QUANT_CONV) THENC
                SIMP_CONV std_ss []
        val c2a_inj = RHS_CONV (RATOR_CONV (RAND_CONV c)) 
        val c2a_no_inj = RHS_CONV (RATOR_CONV (RAND_CONV 
           (BINOP_CONV c))) 
        val c2a = if is_inj then c2a_inj else c2a_no_inj
        val thm2a = CONV_RULE c2a thm1
        val thm2b = CONV_RULE (RHS_CONV (RAND_CONV (RATOR_CONV (RAND_CONV c)))) thm2a
      in
        thm2b
      end

      (* recursive call *)
      val thm3 = let
        val c = PMATCH_LIFT_BOOL_CONV_AUX rc_arg
        val thm3 = CONV_RULE (RHS_CONV (RAND_CONV (RAND_CONV c))) thm2
      in 
        thm3 
      end
    in
      thm3
    end
end

(*

val tm = ``(P2 /\ Q ==> (
  CASE xx OF [
    || (x, y, ys). (x, y::ys) ~> (x + y);
    ||.  (0, []) ~> 9;
    || x.  (x, []) when x > 3 ~> x;
    || x.  (x, []) ~> 0] = 5))``

val tm = ``
  CASE xx OF [
    || (x, y, ys). (x, y::ys) ~> (x + y);
    ||.  (0, []) ~> 9;
    || x.  (x, []) when x > 3 ~> x;
    || x.  (x, []) ~> 0] = 5``
*)


val PMATCH_LIFT_BOOL_CONV_GENCALL_AUX_THM = prove (
 ``(P1 ==> (X1 /\ (P2 ==> X2))) =
   ((P1 ==> X1) /\ ((P1 /\ P2) ==> X2))``,
REWRITE_TAC [IMP_CONJ_THM, AND_IMP_INTRO]);

fun PMATCH_LIFT_BOOL_CONV_GENCALL rc_arg tm = let
  (* check whether we should really process tm *)
  val _ = if type_of tm = bool then () else raise UNCHANGED
  val p_tm = find_term is_PMATCH tm
  fun has_subterm p t = (find_term p t; true) handle HOL_ERR _ => false

  val is_minimal = not (has_subterm (fn t =>
    (not (aconv t tm)) andalso
    (type_of t = bool) andalso
    (has_subterm is_PMATCH t)) tm)
  val _ = if is_minimal then () else raise UNCHANGED

  (* prepare tm *)
  val v = genvar (type_of p_tm)
  val P_tm = mk_abs (v, subst [p_tm |-> v] tm)
  val P_v = genvar (type_of P_tm)

  (* do real work *)
  val thm0 = PMATCH_LIFT_BOOL_CONV_AUX rc_arg (mk_comb (P_v, p_tm))

  (* create conjuncts *)
  val thm1 = let
     fun c t = (REWR_CONV PMATCH_LIFT_BOOL_CONV_GENCALL_AUX_THM THENC
               TRY_CONV (RAND_CONV c)) t
     val thm1a = CONV_RULE (RHS_CONV (RAND_CONV c)) thm0 handle HOL_ERR _ => thm0

     val c = SIMP_CONV (std_ss++boolSimps.CONJ_ss) [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM, GSYM CONJ_ASSOC]
     val thm1b = CONV_RULE (RHS_CONV (EVERY_CONJ_CONV c)) thm1a

     val c = rc_conv rc_arg
     val thm1c = CONV_RULE (RHS_CONV (EVERY_CONJ_CONV c)) thm1b
  in
     thm1c
  end
  
  (* restore original predicate *)
  val thm2 = let
    val thm2a = INST [P_v |-> P_tm] thm1
    val thm2b = CONV_RULE (LHS_CONV BETA_CONV) thm2a
    val thm2c = CONV_RULE (RHS_CONV (DEPTH_CONV BETA_CONV)) thm2b
    val _ = assert (fn thm => aconv (lhs (concl thm)) tm) thm2c
  in
    thm2c
  end   
in
  thm2
end

fun PMATCH_LIFT_BOOL_CONV_GEN ssl = PMATCH_LIFT_BOOL_CONV_GENCALL (ssl, NONE)

val PMATCH_LIFT_BOOL_CONV = PMATCH_LIFT_BOOL_CONV_GEN [];

fun PMATCH_LIFT_BOOL_GEN_ss ssl = 
  make_gen_conv_ss PMATCH_LIFT_BOOL_CONV_GENCALL "PMATCH_LIFT_BOOL_REDUCER" ssl

val PMATCH_LIFT_BOOL_ss = PMATCH_LIFT_BOOL_GEN_ss []


fun PMATCH_TO_TOP_RULE_SINGLE ssl thm = let
  val thm0 = GEN_ALL thm
  val thm1 = CONV_RULE (DEPTH_CONV (PMATCH_LIFT_BOOL_CONV_GEN ssl)) thm0
  val thm2 = CONV_RULE (STRIP_QUANT_CONV (
     EVERY_CONJ_CONV (STRIP_QUANT_CONV (TRY_CONV (RAND_CONV markerLib.stmark_term))))) thm1
  val thm3 = SIMP_RULE std_ss [FORALL_AND_THM, 
   Cong (REFL ``stmarker (t:'a)``)] thm2
  val thm4 = PURE_REWRITE_RULE [markerTheory.stmarker_def] thm3
in 
  thm4
end

fun PMATCH_TO_TOP_RULE_GEN ssl thm = let
  val thms = BODY_CONJUNCTS thm
  val thms' = List.map (PMATCH_TO_TOP_RULE_SINGLE ssl) thms
  val thm0 = LIST_CONJ thms'
  val thm1 = CONV_RULE unwindLib.FLATTEN_CONJ_CONV thm0
in
  thm1
end

fun PMATCH_TO_TOP_RULE thm = PMATCH_TO_TOP_RULE_GEN [] thm;


(***********************************************)
(* Case_splits                                 *)
(* This is work in progress                    *)
(***********************************************)

type column_heuristic = 
   (term * (term list * term) list) list -> int

(* one that uses always the first column *)
val colHeu_first_col : column_heuristic = (fn _ => 0)

(* one that uses always the last column *)
val colHeu_last_col : column_heuristic = (fn cols => length cols - 1)

(* A heuristic based on ranking functions *)
type column_ranking_fun = (term * (term list * term) list) -> int

fun colHeu_rank (rankL : column_ranking_fun list) = (fn colL => let
   val ncolL = Lib.enumerate 0 colL
   fun step rank ncolL = let
     val ranked_cols = List.map (fn (i, c) => ((i, c), rank c)) ncolL
     val max = List.foldl (fn ((_, r), m) => if r > m then r else m) (snd (hd ranked_cols)) (tl ranked_cols)
     val ranked_cols' = List.filter (fn (_, r) => r = max) ranked_cols
     val ncolL' = List.map fst ranked_cols'
   in
     ncolL'
   end
   fun steps [] ncolL = ncolL
     | steps _ [] = []
     | steps _ [e] = [e]
     | steps (rf :: rankL) ncolL = steps rankL (step rf ncolL)
   val ncolL' = steps rankL ncolL
in
   case ncolL' of
      [] => 0 (* something went wrong, should not happen *)
    | ((i, _) :: _) => i
end) : column_heuristic

     
(* ranking functions *)
fun colRank_first_row (_:term, rows) = (
  case rows of
    [] => 0
  | (vs, p) :: _ => 
      if (is_var p andalso mem p vs) then 0 else 1);

fun colRank_first_row_constr db (_, rows) = case rows of
    [] => 0
  | ((vs, p) :: _) => if (is_var p andalso mem p vs) then 0 else
      case pmatch_compile_db_compile_cf db rows of 
        NONE => 0
      | SOME cf => let
          val (exh, constrL) = constructorFamily_get_constructors cf;
          val p_c = fst (strip_comb p)
          val cL_cf = List.map fst constrL;
          val p_c_ok = op_mem same_const p_c cL_cf
        in
          (if p_c_ok then 1 else 0) 
        end handle HOL_ERR _ => 0;

val colRank_constr_prefix : column_ranking_fun = (fn (_, rows) =>
  let fun aux n [] = n
        | aux n ((vs, p) :: pL) = if (is_var p andalso mem p vs) 
             then n else aux (n+1)  pL
  in aux 0 rows end)


fun col_get_constr_set db (_, rows) =
  case pmatch_compile_db_compile_cf db rows of 
    NONE => NONE
  | SOME cf => let
     val (exh, constrL) = constructorFamily_get_constructors cf;
     val cL_rows = List.map (fn (_, p) => fst (strip_comb p)) rows;
     val cL_cf = List.map fst constrL;

     val cL_rows' = List.filter (fn c => op_mem same_const c cL_cf) cL_rows;
     val cL_rows'' = Lib.mk_set cL_rows';
  in
    SOME (cL_rows'', cL_cf, exh)
  end

fun col_get_nonvar_set (_, rows) =
  let
     val cL' = List.filter (fn (vs, p) => 
        not (is_var p andalso mem p vs)) rows;
     val cL'' = Lib.mk_set cL';
  in
    cL''
  end

fun colRank_small_branching_factor db : column_ranking_fun = (fn col =>
  case col_get_constr_set db col of
      SOME (cL, full_constrL, exh) =>
        (~(length cL + (if exh then 0 else 1) + (if length cL = length full_constrL then 0 else 1)))
    | NONE => (~(length (col_get_nonvar_set col) + 2)))

fun colRank_arity db : column_ranking_fun = (fn col =>
  case col_get_constr_set db col of
     SOME (cL, full_constrL, exh) =>
       List.foldl (fn (c, s) => s + length (fst (strip_fun (type_of c)))) 0 cL
   | NONE => 0)


(* heuristics defined using ranking functions *)
val colHeu_first_row = colHeu_rank [colRank_first_row]
val colHeu_constr_prefix = colHeu_rank [colRank_constr_prefix]
fun colHeu_qba db = colHeu_rank [colRank_constr_prefix, colRank_small_branching_factor db, colRank_arity db]
fun colHeu_cqba db = colHeu_rank [colRank_first_row_constr db, 
  colRank_constr_prefix, colRank_small_branching_factor db, colRank_arity db]

(* A list of all the standard heuristics *)
fun colHeu_default cols = colHeu_qba (!thePmatchCompileDB) cols


(*
val t = ``CASE (a,x,xs) OF [
    || x. (NONE,x,[]) ~> x;
    || x. (NONE,x,[2]) ~> x;
    || (x,v18). (NONE,x,[v18]) ~> 3;
    || (x,v12,v16,v17). (NONE,x,v12::v16::v17) ~> 3;
    || (y,x,z,zs). (SOME y,x,[z]) ~> (x + 5 + z);
    || (y,v23,v24). (SOME y,0,v23::v24) ~> (v23 + y);
    || (y,z,v23). (SOME y,SUC z,[v23]) when (y > 5) ~> 3;
    || (y,z). (SOME y,SUC z,[1; 2]) ~> (y + z)
  ]``
*)

fun STRIP_ABS_CONV conv t =
  if (is_abs t) then ABS_CONV (STRIP_ABS_CONV conv) t else
  conv t

fun PMATCH_CASE_SPLIT_AUX rc_arg col_no expand_thm t = let
  val (v, rows) = dest_PMATCH t
  val vs = pairSyntax.strip_pair v

  val arg = el (col_no+1) vs
  val arg_v = genvar (type_of arg)
  val vs' = pairSyntax.list_mk_pair (List.take (vs, col_no) @ (arg_v :: (List.drop (vs, col_no+1))))

  val ff = let
    val (x, xs) = strip_comb t
    val t' = list_mk_comb(x, vs' :: (tl xs))
  in
    mk_abs (arg_v, t')
  end

  val thm0 = ISPEC arg (ISPEC ff expand_thm)
  val thm1 = CONV_RULE (LHS_CONV BETA_CONV) thm0

  val c = SIMP_CONV
    (std_ss++simpLib.merge_ss (fst rc_arg) ++ PMATCH_SIMP_GEN_ss (fst rc_arg)) []
  val thm2 = CONV_RULE (RHS_CONV c) thm1

  (* check whether it got simpler *)
  val _ = if (does_conv_loop thm2) then raise UNCHANGED else ()
in
  thm2
end

(*
val t = t'
val col_no = 1
val rc_arg = ([], NONE)
val db = !thePmatchCompileDB
fun col_heu _ = 0
*)

fun PMATCH_CASE_SPLIT_CONV_GENCALL_STEP (gl, callback_opt) db col_heu t = let
  val _ = if (is_PMATCH t) then () else raise UNCHANGED

  fun find_col cols = if (List.null cols) then raise UNCHANGED else let
    val col_no = col_heu cols
    val (v, col) = el (col_no+1) cols
    val res = pmatch_compile_db_compile db col    
  in
    case res of
        SOME (expand_thm, expand_ss) => (col_no, expand_thm, expand_ss)
      | NONE => let
             val cols' = List.take (cols, col_no) @ List.drop (cols, col_no+1)
             val (col_no', expand_thm, expand_ss) = find_col cols'
             val col_no'' = if (col_no' < col_no) then col_no' else col_no'+1
          in
             (col_no'', expand_thm, expand_ss)
          end
  end

  val (col_no, expand_thm, expand_ss) = find_col (dest_PMATCH_COLS t)
  val thm1 = QCHANGED_CONV (PMATCH_CASE_SPLIT_AUX 
    (expand_ss::gl, callback_opt) col_no expand_thm) t

  (* check whether it got simpler *)
  val _ = if (does_conv_loop thm1) then raise UNCHANGED else ()
in
  thm1
end


val pair_CASE_tm = mk_const ("pair_CASE", ``:'a # 'b -> ('a -> 'b -> 'c) -> 'c``)

fun PMATCH_CASE_SPLIT_CONV_GENCALL rc_arg db col_heu t = let
  val thm0 = PMATCH_SIMP_CONV_GENCALL rc_arg t handle 
        HOL_ERR _ => REFL t
      | UNCHANGED => REFL t
  val t' = rhs (concl thm0)

  val cols = dest_PMATCH_COLS t'
  val col_no = length cols
  val (v, rows) = dest_PMATCH t'

  fun mk_pair avoid acc col_no v = if (col_no <= 1) then (
      let
        val vs = List.rev (v::acc)
        val p = pairSyntax.list_mk_pair vs 
        val rows_tm = listSyntax.mk_list (rows, type_of (hd rows))
      in
        mk_PMATCH p rows_tm
      end
    ) else (
      let
         val (ty1, ty2) = pairSyntax.dest_prod (type_of v)
         val v1 = variant avoid (mk_var ("v", ty1))
         val v2 = variant (v1::avoid) (mk_var ("v", ty2))

         val t0 = inst [alpha |-> ty1, beta |-> ty2, gamma |-> type_of t] pair_CASE_tm
         val t1 = mk_comb (t0, v)
         val t2a = mk_pair (v1::v2::avoid) (v1::acc) (col_no-1) v2
         val t2b = list_mk_abs ([v1, v2], t2a)
         val t2c = mk_comb (t1, t2b)         
      in
        t2c
      end
    )


  val t'' = mk_pair (free_vars t') [] col_no v
  val thm1_tm = mk_eq (t', t'')
  val thm1 = prove (thm1_tm, SIMP_TAC std_ss [pairTheory.pair_CASE_def])

  val thm2 = CONV_RULE (RHS_CONV (
    (TOP_SWEEP_CONV (
      PMATCH_CASE_SPLIT_CONV_GENCALL_STEP rc_arg db col_heu
    )))) thm1

  val thm3 = TRANS thm0 thm2

  (* check whether it got simpler *)
  val _ = if (does_conv_loop thm3) then raise UNCHANGED else ()

  val thm4 = if (has_subterm is_PMATCH (rhs (concl thm3))) then
       thm3 
     else
       CONV_RULE (RHS_CONV REMOVE_REBIND_CONV) thm3
in
  thm4
end

fun PMATCH_CASE_SPLIT_CONV_GEN ssl = PMATCH_CASE_SPLIT_CONV_GENCALL (ssl, NONE)                                      

fun PMATCH_CASE_SPLIT_CONV_HEU col_heu t = 
  PMATCH_CASE_SPLIT_CONV_GEN [] (!thePmatchCompileDB) col_heu t

fun PMATCH_CASE_SPLIT_CONV t = 
  PMATCH_CASE_SPLIT_CONV_HEU colHeu_default t

fun PMATCH_CASE_SPLIT_GEN_ss ssl db col_heu = 
  make_gen_conv_ss (fn rc_arg =>
    PMATCH_CASE_SPLIT_CONV_GENCALL rc_arg db col_heu) 
   "PMATCH_CASE_SPLIT_REDUCER" ssl

fun PMATCH_CASE_SPLIT_HEU_ss col_heu =
  PMATCH_CASE_SPLIT_GEN_ss [] (!thePmatchCompileDB) col_heu

fun PMATCH_CASE_SPLIT_ss () =
  PMATCH_CASE_SPLIT_HEU_ss colHeu_default

end
