structure deepMatchesLib :> deepMatchesLib =
struct

open HolKernel boolLib bossLib
open deepMatchesTheory
open quantHeuristicsLib
open deepMatchesSyntax
open constrFamiliesLib

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

fun rc_ss gl = list_ss ++ simpLib.merge_ss
 (gl @
  [pabs_elim_ss,
   pairSimps.paired_forall_ss,
   pairSimps.paired_exists_ss,
   pairSimps.gen_beta_ss,
   elim_fst_snd_select_ss,
   simpLib.rewrites [
     pairTheory.EXISTS_PROD,
     pairTheory.FORALL_PROD,
     PMATCH_ROW_EQ_NONE,
     PMATCH_ROW_COND_def,
     PAIR_EQ_COLLAPSE,
     oneTheory.one]])

fun callback_CONV cb_opt t = (case cb_opt of
    NONE => raise UNCHANGED
  | SOME cb => (
    if (aconv t T) orelse (aconv t F) then (raise UNCHANGED) else
    (EQT_INTRO (cb t)
     handle HOL_ERR _ => EQF_INTRO (cb (mk_neg t)))))

fun rc_conv (gl, callback_opt) =
  SIMP_CONV (rc_ss gl) [] THENC
  TRY_CONV (callback_CONV callback_opt)

fun rc_tac (gl, callback_opt) =
  CONV_TAC (rc_conv (gl, callback_opt))

fun PMATCH_ROW_ARGS_CONV c =
   RATOR_CONV (RAND_CONV (TRY_CONV c)) THENC
   RATOR_CONV (RATOR_CONV (RAND_CONV (TRY_CONV c))) THENC
   RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV (TRY_CONV c))))


(***********************************************)
(* converting case-splits to PMATCH            *)
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


fun convert_case_aux x t = let
  val (a, ps) = dest_case_fun t

  fun process_arg (p, rh) = let
    val x' = subst [a |-> p] x
  in
    (* recursive call *)
    case convert_case_aux x' rh of
        NONE => [(x', rh)]
      | SOME resl => resl
  end

  val ps = flatten (map process_arg ps)
in
  SOME ps
end handle HOL_ERR _ => NONE;

(* convert a case-term into a PMATCH-term, without any proofs *)
fun convert_case t = let
  val (f, args) = strip_comb t
  val _ = if (List.null args) then failwith "not a case-split" else ()

  val (p,patterns) = if is_literal_case t then (el 2 args, [el 1 args]) else
      (hd args, tl args)
  val v = genvar (type_of p)

  val t0 = if is_literal_case t then list_mk_comb (f, patterns @ [v]) else list_mk_comb (f, v::patterns)
  val ps = case convert_case_aux v t0 of
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

fun PMATCH_INTRO_CONV t = let
  val t' = convert_case t
  val tm = mk_eq (t, t')

  (* very slow, simple approach. Just brute force.
     TODO: change implementation to get more runtime-speed *)
  val my_tac = (
    CASE_TAC THEN
    FULL_SIMP_TAC (rc_ss []) [PMATCH_EVAL, PMATCH_ROW_COND_def]
  )
in
  (* set_goal ([], tm) *)
  prove (tm, REPEAT my_tac)
end handle HOL_ERR _ => raise UNCHANGED


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
val rc_arg = []

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
val PMATCH_CLEANUP_CONV = PMATCH_CLEANUP_CONV_GEN []



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
end handle HOL_ERR _ => raise UNCHANGED


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

fun PMATCH_SIMP_CONV_GENCALL rc_arg = REPEATC (FIRST_CONV [
  CHANGED_CONV (PMATCH_CLEANUP_PVARS_CONV),
  CHANGED_CONV (PMATCH_CLEANUP_CONV_GENCALL rc_arg),
  CHANGED_CONV (PMATCH_REMOVE_ARB_CONV_GENCALL rc_arg),
  CHANGED_CONV (PMATCH_SIMP_COLS_CONV_GENCALL rc_arg),
  CHANGED_CONV (PMATCH_EXPAND_COLS_CONV),
  CHANGED_CONV PMATCH_FORCE_SAME_VARS_CONV
])

fun PMATCH_SIMP_CONV_GEN ssl = PMATCH_SIMP_CONV_GENCALL (ssl, NONE)

val PMATCH_SIMP_CONV = PMATCH_SIMP_CONV_GEN []

fun PMATCH_SIMP_convdata_conv ssl callback back =
  PMATCH_SIMP_CONV_GENCALL (ssl, SOME (callback back))


fun PMATCH_SIMP_GEN_ss ssl = simpLib.conv_ss
  { name = "PMATCH_SIMP_CONV",
    key = SOME ([], ``(PMATCH (v:'a) rows):'b``),
    trace = 1,
    conv = PMATCH_SIMP_convdata_conv ssl
  }

val PMATCH_SIMP_ss = PMATCH_SIMP_GEN_ss []



(***********************************************)
(* Case_splits                                 *)
(* This is work in progress                    *)
(***********************************************)

(*
val t = ``
PMATCH (a,x,xs)
     [PMATCH_ROW (\x. (NONE,x,[])) (\x. T) (\x. x);
      PMATCH_ROW (\x. (NONE,x,[2])) (\x. T) (\x. x);
      PMATCH_ROW (\ (x,v18). (NONE,x,[v18])) (\ (x, v18). T) (\ (x, v18). 3);
      PMATCH_ROW (\ (x,v12,v16,v17). (NONE,x,v12::v16::v17))
                 (\ (x,v12,v16,v17). T)
                 (\ (x,v12,v16,v17). 3);
      PMATCH_ROW (\ (y,x,z,zs). (SOME y,x,[z]))
                 (\ (y,x,z,zs). T)
                 (\ (y,x,z,zs). x+5+z);
      PMATCH_ROW (\ (y,v23,v24). (SOME y,0,v23::v24))
                 (\ (y,v23,v24). T)
                 (\ (y,v23,v24). v23+y);
      PMATCH_ROW (\ (y,z,v23). (SOME y,SUC z,[v23]))
                 (\ (y,z,v23). y > 5)
                 (\ (y,z,v23). 3);
      PMATCH_ROW (\ (y,z). (SOME y,SUC z,[1; 2]))
                 (\ (y,z). T)
                 (\ (y,z). y + z)
   ]``
*)

fun STRIP_ABS_CONV conv t =
  if (is_abs t) then ABS_CONV (STRIP_ABS_CONV conv) t else
  conv t

fun PMATCH_CASE_SPLIT_AUX col expand_thm conv t = let
  val (v, rows) = dest_PMATCH t
  val vs = pairSyntax.strip_pair v

  val arg = el (col+1) vs
  val arg_v = genvar (type_of arg)
  val vs' = pairSyntax.list_mk_pair (List.take (vs, col) @ (arg_v :: (List.drop (vs, col+1))))

  val ff = let
    val (x, xs) = strip_comb t
    val t' = list_mk_comb(x, vs' :: (tl xs))
  in
    mk_abs (arg_v, t')
  end

  val thm0 = ISPEC arg (ISPEC ff expand_thm)
  val thm1 = CONV_RULE (LHS_CONV BETA_CONV) thm0

  fun is_case_conv_end t =
    is_comb (fst (dest_comb t)) handle HOL_ERR _ => false

  fun case_conv conv t =
    if not (is_case_conv_end t) then REFL t else
    (RAND_CONV (STRIP_ABS_CONV conv) THENC RATOR_CONV (case_conv conv)) t

  val thm2 = CONV_RULE (RHS_CONV (case_conv (BETA_CONV THENC TRY_CONV conv))) thm1
in
  thm2
end


fun PMATCH_CASE_SPLIT_CONV_GENCALL rc_arg col_no t = let
  val thm0 = QCHANGED_CONV (
      PMATCH_SIMP_CONV_GENCALL rc_arg) t handle HOL_ERR _ => REFL t

  val t' = rhs (concl thm0)

  val (v, col) = el (col_no+1) (dest_PMATCH_COLS t')

  val expand_thm = get_case_expand_thm (v, col)

  val thm1 = QCHANGED_CONV (PMATCH_CASE_SPLIT_AUX col_no expand_thm (PMATCH_SIMP_CONV_GENCALL rc_arg)) t' handle HOL_ERR _ => (REFL t')
in
  TRANS thm0 thm1
end

end
