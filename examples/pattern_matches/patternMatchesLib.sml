structure patternMatchesLib :> patternMatchesLib =
struct

open HolKernel boolLib bossLib
open patternMatchesTheory
open simpLib
open quantHeuristicsLib
open DatatypeSimps
open patternMatchesSyntax
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

val PAIR_EQ_COLLAPSE = prove (
``(((FST x = (a:'a)) /\ (SND x = (b:'b))) = (x = (a, b)))``,
Cases_on `x` THEN SIMP_TAC std_ss [])

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

(* A basic simpset-fragment with a lot of useful stuff
   to automatically show the validity of preconditions
   as produced by functions in this library. *)
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
     PMATCH_ROW_COND_EX_def,
     PAIR_EQ_COLLAPSE,
     oneTheory.one]];

(* We add the stateful rewrite set (to simplify
   e.g. case-constants or constructors) and a
   custum component as well. *)
fun rc_ss gl = srw_ss() ++ simpLib.merge_ss (static_ss :: gl)

(* finally we add a call-back component. This is an
   external conversion that is used at the end if
   everything else fails. This is used to have nested calls
   of the simplifier. The simplifier executes some conversion that
   uses rs_ss. At the end, we might want to use the external
   simplifier. This is realised with these call-backs. *)
fun callback_CONV cb_opt t = (case cb_opt of
    NONE => NO_CONV t
  | SOME cb => cb t)

fun rc_conv_rws (gl, callback_opt) thms = REPEATC (
  SIMP_CONV (rc_ss gl) thms THENC
  TRY_CONV (callback_CONV callback_opt))

(* So, now combine it to get some convenient high-level
   functions. *)
fun rc_conv rc_arg = rc_conv_rws rc_arg []

fun rc_tac (gl, callback_opt) =
  CONV_TAC (rc_conv (gl, callback_opt))

fun rc_elim_precond rc_arg thm = let
  val pre = rand (rator (concl thm))
  val pre_thm = prove_attempt (pre, rc_tac rc_arg)
  val thm2 = MP thm pre_thm
in
  thm2
end

(* fix_appends expects a theorem of the form
   PMATCH v rows = PMATCH v' rows'

   and a term l of form
   PMATCH v rows0.

   It tries to get the appends in rows and rows' in
   a nice form. To do this, it tries to prove that
   l and the lhs of the theorem are equal.
   Then it tries to simplify appends in rows'
   resulting in rows''.

   It returns a theorem of the form

   l = PMATCH v' rows''.
*)
fun fix_appends rc_arg l thm = let
  val t_eq_thm = prove (mk_eq (l, lhs (concl thm)),
     CONV_TAC (DEPTH_CONV listLib.APPEND_CONV) THEN
     rc_tac rc_arg)

  val thm2 = TRANS t_eq_thm thm

  fun my_append_conv t = let
    val _ = if listSyntax.is_append t then () else raise UNCHANGED
  in
    (BINOP_CONV (TRY_CONV my_append_conv) THENC
     listLib.APPEND_CONV) t
  end

  val thm3 = CONV_RULE (RHS_CONV (RAND_CONV my_append_conv)) thm2
    handle HOL_ERR _ => thm2
         | UNCHANGED => thm2
in
  thm3
end

(* Apply a conversion to all args of a PMATCH_ROW, i.e. given
   a term of the form ``PMATCH_ROW pat guard rhs i``
   it applies a conversion to ``pat`` ``guard`` and ``rhs``. *)
fun PMATCH_ROW_ARGS_CONV c =
   RATOR_CONV (RAND_CONV (TRY_CONV c)) THENC
   RATOR_CONV (RATOR_CONV (RAND_CONV (TRY_CONV c))) THENC
   RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV (TRY_CONV c))))


(***********************************************)
(* converting between case-splits to PMATCH    *)
(***********************************************)

(* ----------------------- *)
(* Auxiliary functions for *)
(* case2pmatch             *)
(* ----------------------- *)

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


(* try to collapse rows by introducing a catchall at end*)
fun dest_case_fun_collapse (a, ps) = let

  (* find all possible catch-all clauses *)
  fun check_collapsable (p, rh) = let
     val p_vs = FVL [p] empty_tmset
     val rh' = if HOLset.isEmpty p_vs then rh else
        Term.subst [p |-> a] rh
     val ok = HOLset.isEmpty (HOLset.intersection (FVL [rh'] empty_tmset, p_vs))
  in
    if ok then SOME rh' else NONE
  end

  val catch_all_cands = List.foldl (fn (prh, cs) =>
      case check_collapsable prh of
         NONE => cs
       | SOME rh => rh::cs) [] ps

  (* really collapse *)
  fun is_not_cought ca (p, rh) =
     not (aconv rh (Term.subst [a |-> p] ca))

  val all_collapse_opts = List.map (fn ca => (ca, filter (is_not_cought ca) ps)) catch_all_cands

  val all_collapse_opts_sorted = sort (fn (_, l1) => fn (_, l2) => List.length l1 < List.length l2) all_collapse_opts

  (* could we collapse 2 cases? *)
in
  if (List.null all_collapse_opts) then (a, ps) else
  let
     val (ca', ps') = hd all_collapse_opts_sorted
  in if (List.length ps' + 1 < List.length ps) then
        (a, (ps' @ [(a, ca')]))
      else (a, ps)
  end
end

fun case2pmatch_aux optimise x t = let
  val (a, ps) = dest_case_fun t
  val (a, ps) = if optimise then (dest_case_fun_collapse (a, ps)) else (a, ps)

  fun process_arg (p, rh) = let
    val x' = subst [a |-> p] x
  in
    (* recursive call *)
    case case2pmatch_aux optimise x' rh of
        NONE => [(x', rh)]
      | SOME resl => resl
  end

  val ps = flatten (map process_arg ps)
in
  SOME ps
end handle HOL_ERR _ => NONE;

fun case2pmatch_remove_unnessary_rows ps = let
  fun mk_distinct_rows (p1, _) (p2, rh2) = let
     val avoid = free_vars p1
     val (s, _) = List.foldl (fn (v, (s, av)) =>
       let val v' = variant av v in
       ((v |-> v')::s, v'::av) end) ([], avoid) (free_vars p2)
     val p2' = Term.subst s p2
     val rh2' = Term.subst s rh2
  in
     (p2', rh2')
  end

  fun pats_unify (p1, _) (p2, _) = (
    (Unify.simp_unify_terms [] p1 p2; true) handle HOL_ERR _ => false
  )

  fun row_subsumed (p1, rh1) (p2, rh2) = let
     val (s, _) = match_term p2 p1
     val rh2' = Term.subst s rh2
  in aconv rh2' rh1 end handle HOL_ERR _ => false

  fun row_is_needed r1 rs = case rs of
      [] => true
    | r2::rs' => let
         val r2' = mk_distinct_rows r1 r2
      in
         if pats_unify r1 r2' then (
           not (row_subsumed r1 r2')
         ) else row_is_needed r1 rs'
      end

   fun check_rows acc rs = case rs of
       [] => List.rev acc
     | [_] => (* drop last one *) List.rev acc
     | r::rs' => check_rows (if row_is_needed r rs' then r::acc else acc)
                  rs'

   val ps' = case ps of
                [] => []
              | (p, rh)::_ => (ps @ [(genvar (type_of p), mk_arb (type_of rh))])

in
  check_rows [] ps'
end


(* ----------------------- *)
(* End Auxiliary functions *)
(* for case2pmatch         *)
(* ----------------------- *)

(*
val (p1, rh1) = el 5 ps
val (p2, rh2) = mk_distinct_rows (p1, rh1) (el 6 ps)
ps
*)

(* convert a case-term into a PMATCH-term, without any proofs *)
fun case2pmatch opt t = let
  val (f, args) = strip_comb t
  val _ = if (List.null args) then failwith "not a case-split" else ()

  val (p,patterns) = if is_literal_case t then (el 2 args, [el 1 args]) else
      (hd args, tl args)
  val v = genvar (type_of p)

  val t0 = if is_literal_case t then list_mk_comb (f, patterns @ [v]) else list_mk_comb (f, v::patterns)
  val ps = case case2pmatch_aux opt v t0 of
      NONE => failwith "not a case-split"
    | SOME ps => ps

  val ps = if opt then case2pmatch_remove_unnessary_rows ps else ps

  fun process_pattern (p, rh) = let
    val fvs = List.rev (free_vars p)
  in
    if opt then
      snd (mk_PMATCH_ROW_PABS_WILDCARDS fvs (p, T, rh))
    else
      mk_PMATCH_ROW_PABS fvs (p, T, rh)
  end
  val rows = List.map process_pattern ps
  val rows_tm = listSyntax.mk_list (rows, type_of (hd rows))

  val rows_tm_p = Term.subst [v |-> p] rows_tm
in
  mk_PMATCH p rows_tm_p
end

(* So far, we converted a classical case-expression
   to a PMATCH without any proof. The following is used
   to prove the equivalence of the result via repeated
   case-splits and evaluation. This allows to
   define some conversions then. *)

val COND_CONG_STOP = prove (``
  (c = c') ==> ((if c then x else y) = (if c' then x else y))``,
SIMP_TAC std_ss [])

fun case_pmatch_eq_prove t t' = let
  val tm = mk_eq (t, t')

  (* very slow, simple approach. Just brute force.
     TODO: change implementation to get more runtime-speed *)
  val my_tac = (
    REPEAT (BasicProvers.TOP_CASE_TAC THEN
            ASM_REWRITE_TAC[]) THEN
    FULL_SIMP_TAC (rc_ss []) [PMATCH_EVAL, PMATCH_ROW_COND_def,
      PMATCH_INCOMPLETE_def]
  )
in
  (* set_goal ([], tm) *)
  prove (tm, REPEAT my_tac)
end handle HOL_ERR _ => raise UNCHANGED


fun PMATCH_INTRO_CONV t =
  case_pmatch_eq_prove t (case2pmatch true t)

fun PMATCH_INTRO_CONV_NO_OPTIMISE t =
  case_pmatch_eq_prove t (case2pmatch false t)


(* ------------------------- *)
(* pmatch2case               *)
(* ------------------------- *)

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
(* removing redundant rows                     *)
(***********************************************)

(*
val rc_arg = ([], NONE)

set_trace "parse deep cases" 0

val t = ``
   CASE l OF [
     ||. [] ~> 0;
     || (x,y). x::y::x::y::_ ~> (x + y);
     ||! x::x::x::x::_ when (x > 10) ~> x;
     ||! x::x::x::x::x::_ ~> 9;
     ||. [] ~> 1;
     ||! x::x::x::y::_ ~> (x + x + x);
     || x. x::_ ~> 1;
     ||! x::y::z::_ ~> (x + x + x)
   ]``

val (rows, _) = listSyntax.dest_list (rand t)
*)

(* For removing redundant rows we want to check whether
   the pattern of a row is overlapped by the pattern of a
   previous row. In preparation for this, we extract all
   patterns and generate fresh variables for it. The we
   build for all rows the pair of the pattern + the patterns
   of all following rows. This allows for simple checks
   via matching later. *)
fun compute_row_pat_pairs rows = let
  (* get pats with fresh vars to do a quick prefiltering *)
  val pats_unique = Lib.enumerate 0 (Lib.mapfilter (fn r => let
    val (p, _, _) = dest_PMATCH_ROW r
    val (vars_tm, pb) = pairSyntax.dest_pabs p
    val vars = pairSyntax.strip_pair vars_tm
    val s = List.map (fn v => (v |-> genvar (type_of v))) vars
    val pb' = subst s pb
  in
    pb'
  end) rows)

  (* get all pairs, first component always appears before second *)
  val candidates = let
    fun aux acc l = case l of
       [] => acc
     | (x::xs) => aux ((List.map (fn y => (x, y)) xs) @ acc) xs
  in
    aux [] pats_unique
  end
in
  candidates
end

(* Now do the real filtering *)
fun PMATCH_REMOVE_FAST_REDUNDANT_CONV_GENCALL_SINGLE rc_arg t = let
  val (v, rows) = dest_PMATCH t
  val candidates = compute_row_pat_pairs rows

  (* quick filter on matching *)
  val candidates_match = let
     fun does_match ((_, p1), (_, p2)) =
        can (match_term p1) p2
  in
     List.filter does_match candidates
  end

  (* filtering finished, now try it for real *)
  val cands = List.map (fn ((p1, _), (p2, _)) => (p1, p2)) candidates_match
  (* val (r_no1, r_no2) = el 1 cands *)
  fun try_pair (r_no1, r_no2) = let
    val tm0 = let
      val rows1 = List.take (rows, r_no1)
      val r1 = List.nth (rows, r_no1)
      val rows_rest = List.drop (rows, r_no1+1)
      val rows2 = List.take (rows_rest, (r_no2 - r_no1 - 1))
      val r2 = List.nth (rows, r_no2)
      val rows3 = List.drop (rows_rest, r_no2 - r_no1)

      val rows1_tm = listSyntax.mk_list (rows1, type_of r1)
      val rows2_tm = listSyntax.mk_list (rows2, type_of r1)
      val r1rows2_tm = listSyntax.mk_cons (r1, rows2_tm)
      val rows3_tm = listSyntax.mk_list (rows3, type_of r1)
      val r2rows3_tm = listSyntax.mk_cons (r2, rows3_tm)

      val arg = listSyntax.list_mk_append [rows1_tm, r1rows2_tm, r2rows3_tm]
    in
      mk_PMATCH v arg
    end

    val thm0 = FRESH_TY_VARS_RULE PMATCH_ROWS_DROP_REDUNDANT_PMATCH_ROWS
    val thm1 = PART_MATCH (lhs o rand) thm0 tm0

    val thm2 = rc_elim_precond rc_arg thm1
    val thm3 = fix_appends rc_arg t thm2
  in
    thm3
  end
in
  Lib.tryfind try_pair cands
end handle HOL_ERR _ => raise UNCHANGED

fun PMATCH_REMOVE_FAST_REDUNDANT_CONV_GENCALL rc_arg = REPEATC (PMATCH_REMOVE_FAST_REDUNDANT_CONV_GENCALL_SINGLE rc_arg)
fun PMATCH_REMOVE_FAST_REDUNDANT_CONV_GEN ssl = PMATCH_REMOVE_FAST_REDUNDANT_CONV_GENCALL (ssl, NONE)
val PMATCH_REMOVE_FAST_REDUNDANT_CONV = PMATCH_REMOVE_FAST_REDUNDANT_CONV_GEN []


(***********************************************)
(* removing subsumed rows                       *)
(***********************************************)

(*
val rc_arg = ([], NONE)

set_trace "parse deep cases" 0
val t = case2pmatch false ``case x of NONE => 0``

val t = case2pmatch false ``case (x, y, z) of
   (0, y, z) => 2
 | (x, NONE, []) => x
 | (x, SOME y, l) => x+y``

val t =
   ``CASE (x,y,z) OF [
    || v1. (0,v1) ~> 2;
    || v4. (SUC v4,NONE,[]) ~> (SUC v4);
    || (v4,v10,v11). (SUC v4,NONE,v10::v11) ~> ARB;
    || v4. (v4,NONE,_) ~> v4;
    || (v4,v10,v11). (0,SOME _ ,_) ~> ARB;
    || (v4,v9,v8). (SUC v4,SOME v9,v8) ~> (SUC v4 + v9)
  ]``

*)

(* When removing subsumed rows, i.e. rows that can be dropped,
   because a following rule covers them, we can sometimes drop rows with
   right-hand-side ARB, because PMATCH v [] evalutates to ARB.
   This is semantically fine, but changes the users-view. The resulting
   case expression might e.g. not be exhaustive any more. This can
   also cause trouble for code generation. Therefore the parameter
   [exploit_match_exp] determines, whether this optimisation is performed. *)
fun PMATCH_REMOVE_SUBSUMED_CONV_GENCALL_SINGLE
  exploit_match_exp rc_arg t = let
  val (v, rows) = dest_PMATCH t
  val candidates = compute_row_pat_pairs rows

  (* quick filter on matching *)
  val candidates_match = let
     fun does_match ((_, p1), (_, p2)) =
        can (match_term p2) p1
  in
     List.filter does_match candidates
  end

  (* filtering finished, now try it for real *)
  val cands_sub = List.map (fn ((p1, _), (p2, _)) => (p1, SOME p2)) candidates_match

  val cands_arb = Lib.mapfilter (fn (i, r) => let
     val (_, _, _, r) = dest_PMATCH_ROW_ABS r in
   (dest_arb r; (i, (NONE : int option))) end) (Lib.enumerate 0 rows)

  val cands = if exploit_match_exp then (cands_sub @ cands_arb) else
    cands_sub

  (* val (r_no1, r_no2_opt) = el 2 cands_arb *)
  fun try_pair (r_no1, r_no2_opt) = let
    fun mk_row_list rs = listSyntax.mk_list (rs, type_of (hd rows))

    fun extract_el_n n rs = let
      val rows1 = List.take (rs, n)
      val r1 = List.nth (rs, r_no1)
      val rows_rest = List.drop (rs, r_no1+1)
      val rows1_tm = mk_row_list rows1

      fun build_tm rest_tm =
        listSyntax.mk_append (rows1_tm,
          (listSyntax.mk_cons (r1, rest_tm)))
    in
      (rows_rest, build_tm)
    end

    val tm0 = let
       val (rs_rest, bf_1) = extract_el_n r_no1 rows

       val rs2 = case r_no2_opt of
           NONE => mk_row_list rs_rest
         | SOME n => let
             val n' = n - r_no1 - 1
             val (rs_rest', bf_2) = extract_el_n n' rs_rest
           in
             bf_2 (mk_row_list rs_rest')
           end
    in
      mk_PMATCH v (bf_1 rs2)
    end

    val thm_base = case r_no2_opt of
        NONE => PMATCH_REMOVE_ARB_NO_OVERLAP
      | SOME _ => PMATCH_ROWS_DROP_SUBSUMED_PMATCH_ROWS
    val thm0 = FRESH_TY_VARS_RULE thm_base
    val thm1 = PART_MATCH (lhs o rand) thm0 tm0

    val thm2 = rc_elim_precond rc_arg thm1
    val thm3 = fix_appends rc_arg t thm2
  in
    thm3
  end
in
  Lib.tryfind try_pair cands
end handle HOL_ERR _ => raise UNCHANGED

fun PMATCH_REMOVE_SUBSUMED_CONV_GENCALL eme rc_arg = REPEATC (PMATCH_REMOVE_SUBSUMED_CONV_GENCALL_SINGLE eme rc_arg)
fun PMATCH_REMOVE_SUBSUMED_CONV_GEN eme ssl = PMATCH_REMOVE_SUBSUMED_CONV_GENCALL eme (ssl, NONE)
fun PMATCH_REMOVE_SUBSUMED_CONV eme = PMATCH_REMOVE_SUBSUMED_CONV_GEN eme []


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

(* This can also be considered partial evaluation *)

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
  CHANGED_CONV (PMATCH_REMOVE_FAST_REDUNDANT_CONV_GENCALL rc_arg),
  CHANGED_CONV (PMATCH_REMOVE_SUBSUMED_CONV_GENCALL true rc_arg),
  CHANGED_CONV (PMATCH_SIMP_COLS_CONV_GENCALL rc_arg),
  CHANGED_CONV (PMATCH_EXPAND_COLS_CONV),
  CHANGED_CONV PMATCH_FORCE_SAME_VARS_CONV,
  PMATCH_INTRO_WILDCARDS_CONV,
  REWR_CONV (CONJUNCT1 PMATCH_def)
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
(* Remove double var bindings                  *)
(***********************************************)

fun force_unique_vars s no_change avoid t =
  case Psyntax.dest_term t of
      Psyntax.VAR (_, _) =>
      if (mem t no_change) then (s, avoid, t) else
      let
         val v' = variant avoid t
         val avoid' = v'::avoid
         val s' = if (v' = t) then s else ((v', t)::s)
      in (s', avoid', v') end
    | Psyntax.CONST _ => (s, avoid, t)
    | Psyntax.LAMB (v, t') => let
         val (s', avoid', t'') = force_unique_vars s (v::no_change)
           (v::avoid) t'
      in
         (s', avoid', mk_abs (v, t''))
      end
    | Psyntax.COMB (t1, t2) => let
         val (s', avoid', t1') = force_unique_vars s no_change avoid t1
         val (s'', avoid'', t2') = force_unique_vars s' no_change avoid' t2
      in
         (s'', avoid'', mk_comb (t1', t2'))
      end;

(*
val row = ``PMATCH_ROW (\ (x,y). (x, SOME y, SOME x, SOME z, (x+z)))
              (\ (x, y). P x y) (\ (x, y). f x y)``

val row = ``PMATCH_ROW (\ (x,y). (x, SOME y, SOME z, SOME z, (z+z)))
              (\ (x, y). P x y) (\ (x, y). f x y)``
*)

fun PMATCH_ROW_REMOVE_DOUBLE_BIND_CONV_GENCALL rc_arg row = let
  val _ = if not (is_PMATCH_ROW row) then raise UNCHANGED else ()
  val (p_t, g_t, r_t) = dest_PMATCH_ROW row
  val (vars_tm, p_tb) = pairSyntax.dest_pabs p_t
  val vars = pairSyntax.strip_pair vars_tm

  val (new_binds, _, p_tb') = force_unique_vars [] (free_vars p_t) [] p_tb
  val _ = if List.null new_binds then raise UNCHANGED else ()

  val vars' = vars @ (List.map fst new_binds)
  val g_v = genvar (type_of g_t)
  val r_v = genvar (type_of r_t)


  val g_t' = list_mk_conj ((List.map mk_eq new_binds)@[mk_comb (g_v, vars_tm)])
  val r_t' = mk_comb (r_v, vars_tm)

  val row' = mk_PMATCH_ROW_PABS vars' (p_tb', g_t', r_t')
  val row0 = mk_PMATCH_ROW (p_t, g_v, r_v)

  val thm0_tm = mk_eq (row0, row')
  val thm0 = let
    val thm0 = FRESH_TY_VARS_RULE PMATCH_ROW_REMOVE_DOUBLE_BINDS_THM
    val g_tm = pairSyntax.mk_pabs (vars_tm,
      subst (List.map (fn (v, v') => (v |-> v')) new_binds)
        (pairSyntax.list_mk_pair vars'))
    val thm1 = ISPEC g_tm thm0
    val thm2 = PART_MATCH rand thm1 thm0_tm
    val thm3 = rc_elim_precond rc_arg thm2
  in
    thm3
  end

  val thm1 = INST [(g_v |-> g_t), (r_v |-> r_t)] thm0

  val thm1a_tm = mk_eq (row, lhs (concl thm1))
  val thm1a = prove (thm1a_tm, rc_tac rc_arg)

  val thm2 = TRANS thm1a thm1

  val thm3 = CONV_RULE (RHS_CONV (DEPTH_CONV pairLib.GEN_BETA_CONV))
    thm2
in
  thm3
end handle HOL_ERR _ => raise UNCHANGED

fun PMATCH_REMOVE_DOUBLE_BIND_CONV_GENCALL rc_arg t =
  PMATCH_ROWS_CONV (PMATCH_ROW_REMOVE_DOUBLE_BIND_CONV_GENCALL
    rc_arg) t

fun PMATCH_REMOVE_DOUBLE_BIND_CONV_GEN ssl =
  PMATCH_REMOVE_DOUBLE_BIND_CONV_GENCALL (ssl, NONE)

val PMATCH_REMOVE_DOUBLE_BIND_CONV = PMATCH_REMOVE_DOUBLE_BIND_CONV_GEN [];

fun PMATCH_REMOVE_DOUBLE_BIND_GEN_ss ssl =
  make_gen_conv_ss PMATCH_ROW_REMOVE_DOUBLE_BIND_CONV_GENCALL "PMATCH_REMOVE_DOUBLE_BIND_REDUCER" ssl

val PMATCH_REMOVE_DOUBLE_BIND_ss = PMATCH_REMOVE_DOUBLE_BIND_GEN_ss []


(***********************************************)
(* Remove a GUARD                              *)
(***********************************************)

(*
val t = ``
PMATCH (y,x,l)
     [PMATCH_ROW (\x. (SOME 0,x,[]))  (\x. T) (\x. x);
      PMATCH_ROW (\z. (SOME 1,z,[2])) (\z. F) (\z. z);
      PMATCH_ROW (\x. (SOME 3,x,[2])) (\x. IS_SOME x) (\x. x);
      PMATCH_ROW (\(z,y). (y,z,[2]))  (\(z, y). IS_SOME y) (\(z, y). y);
      PMATCH_ROW (\z. (SOME 1,z,[2])) (\z. F) (\z. z);
      PMATCH_ROW (\x. (SOME 3,x,[2])) (\x. IS_SOME x) (\x. x)
   ]``

val rc_arg = ([], NONE)
val rows = 0
*)


fun PMATCH_REMOVE_GUARD_AUX rc_arg t = let
  val (v, rows) = dest_PMATCH t

  fun find_row_to_split rs1 rs = case rs of
     [] => raise UNCHANGED (* nothing found *)
   | (r:: rs') => let
        val (_, _, g, _) = dest_PMATCH_ROW_ABS r
        val g_simple = ((g = T) orelse (g = F))
     in
        if g_simple then
           find_row_to_split (r::rs1) rs'
        else let
          val r_ty = type_of r
          val rs1_tm = listSyntax.mk_list (List.rev rs1, r_ty)
          val rs2_tm = listSyntax.mk_list (rs', r_ty)
        in
           (rs1_tm, r, rs2_tm)
        end
     end

  val (rs1, r, rs2) = find_row_to_split [] rows

  val thm = let
    val thm0 = FRESH_TY_VARS_RULE GUARDS_ELIM_THM
    val (p_tm, g_tm, r_tm) = dest_PMATCH_ROW r
    val thm1 = ISPECL [v, rs1, rs2, p_tm, g_tm, r_tm] thm0

    val thm2 = rc_elim_precond rc_arg thm1
    val thm3 = fix_appends rc_arg t thm2
  in
    thm3
  end

  val thm2 = CONV_RULE (RHS_CONV (RAND_CONV (RAND_CONV (RATOR_CONV (RAND_CONV PMATCH_ROW_FORCE_SAME_VARS_CONV))))) thm

in
  thm2
end handle HOL_ERR _ => raise UNCHANGED



fun PMATCH_REMOVE_GUARDS_CONV_GENCALL rc_arg t = let
  val thm0 = REPEATC (PMATCH_REMOVE_GUARD_AUX rc_arg) t
  val m_ss = simpLib.merge_ss (fst rc_arg)
  val c = SIMP_CONV (std_ss ++ m_ss ++
    PMATCH_SIMP_GEN_ss (fst rc_arg)) []
  val thm1 = CONV_RULE (RHS_CONV c) thm0
in
  thm1
end handle HOL_ERR _ => raise UNCHANGED


fun PMATCH_REMOVE_GUARDS_CONV_GEN ssl = PMATCH_REMOVE_GUARDS_CONV_GENCALL (ssl, NONE)

val PMATCH_REMOVE_GUARDS_CONV = PMATCH_REMOVE_GUARDS_CONV_GEN [];

fun PMATCH_REMOVE_GUARDS_GEN_ss ssl =
  make_gen_conv_ss PMATCH_REMOVE_GUARDS_CONV_GENCALL "PMATCH_REMOVE_GUARDS_REDUCER" ssl

val PMATCH_REMOVE_GUARDS_ss = PMATCH_REMOVE_GUARDS_GEN_ss []


(***********************************************)
(* Lifting to lowest boolean level             *)
(***********************************************)

(* One can replace pattern matches with a big-conjunction.
   Each row becomes one conjunct. Since the conjunction is
   of type bool, this needs to be done at a boolean level.
   So we can replace an arbitry term

   P (PMATCH i rows) with

   (row_cond 1 i -> P (row_rhs 1)) /\
   ...
   (row_cond n i -> P (row_rhs n)) /\

   The row-cond contains that the pattern does not overlap with
   any previous pattern, that the guard holds.

   The most common use-case of lifting are function definitions.
   of the form

   f x = PMATCH x rows

   which can be turned into a conjunction of top-level
   rewrite rules for the function f.
*)

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
        val thm02 = rc_elim_precond rc_arg thm01
      in
        (thm02, true)
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
(* PATTERN COMPILATION                         *)
(***********************************************)

(* A column heuristic is a function that chooses the
   next column to perform a case split on.
   It gets a list of columns of the pattern match, i.e.
   the input value + a list of the patterns in each row.
   The patterns are represented as a pair of
   a list of free variables and the real pattern. *)
type column = (term * (term list * term) list)
type column_heuristic = column list -> int

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


(* Now we can define a case-split function that performs
   case-splits using such heuristics. *)

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
val col_heu = colHeu_default
*)

fun PMATCH_CASE_SPLIT_CONV_GENCALL_STEP (gl, callback_opt) db col_heu t = let
  val _ = if (is_PMATCH t) then () else raise UNCHANGED

  fun find_col cols = if (List.null cols) then raise UNCHANGED else let
    val col_no = col_heu cols
    val (v, col) = el (col_no+1) cols
    val res = pmatch_compile_db_compile db col
  in
    case res of
        SOME (expand_thm, _, expand_ss) => (col_no, expand_thm, expand_ss)
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


(***********************************************)
(* COMPUTE CASE-DISTINCTION based on pats      *)
(***********************************************)

(*
val t = ``
  CASE (a,x,xs) OF [
    ||. (NONE,_,[]) ~> 0;
    || x. (NONE,x,[]) when x < 10 ~> x;
    || x. (NONE,x,[2]) ~> x;
    ||! (NONE,x,[v18]) ~> 3;
    ||! (NONE,_,[_;_]) ~> x;
    || (x,v12,v16,v17). (NONE,x,v12::v16::v17) ~> 3;
    || (y,x,z,zs). (SOME y,x,[z]) ~> x + 5 + z;
    || (y,v23,v24). (SOME y,0,v23::v24) ~> (v23 + y);
    || (y,z,v23). (SOME y,SUC z,[v23]) when y > 5 ~> 3;
    || (y,z). (SOME y,SUC z,[1; 2]) ~> y + z
  ]``;

  val (v, rows) = dest_PMATCH t
  val pats = List.map (#1 o dest_PMATCH_ROW) rows

  val col_heu = colHeu_default
  val db = !thePmatchCompileDB

  val pats = [``\(x:num). 2``]
  val pats = [``\(x:num). [2;3;4]``]

*)

local

  val case_dist_exists_thm = prove (``!Q. (
    (!(x:'a). Q x) ==>
    !P. (?x. P x) = (?x. Q x /\ P x))``,
  SIMP_TAC std_ss []);

  val label_over_or_thm = prove (
    ``(lbl :- (t1 \/ t2)) <=> (lbl :- t1) \/ (lbl :- t2)``,
    REWRITE_TAC[markerTheory.label_def]);

  fun find_nchotomy_for_cols db col_heu cols = let
    val _ = if (List.null cols) then
       raise failwith "compile failed" else ()
    val col_no = col_heu cols
    val (v, col) = el (col_no+1) cols
    val nchot_thm_opt = pmatch_compile_db_compile_nchotomy db col
  in
    case nchot_thm_opt of
      SOME nchot_thm => (v, ISPEC v nchot_thm)
    | NONE => let
        val cols' = List.take (cols, col_no) @ List.drop (cols, col_no+1)
      in
        find_nchotomy_for_cols db col_heu cols'
      end
  end


  fun mk_initial_state var_gen lbl_gen pats = let
    val (_, p) = pairSyntax.dest_pabs (hd pats)
    val cs = pairLib.strip_pair p
    val vs = List.map (fn p => var_gen (type_of p)) cs
    val initial_value = pairLib.list_mk_pair vs
    val cols = dest_PATLIST_COLS initial_value pats

    val lbl = lbl_gen ()
    val initial_thm = let
      val x_tm = mk_var ("x", type_of initial_value)
      val tm = mk_forall (x_tm, markerSyntax.mk_label (lbl, list_mk_exists (vs, mk_eq (x_tm, initial_value))))
      val thm = prove (tm,
        SIMP_TAC std_ss [pairTheory.FORALL_PROD, markerTheory.label_def])
    in thm end
  in
    (initial_thm, cols, lbl)
  end


  fun compute_cases_info var_gen lbl_gen v nthm = let
    val disjuncts = ref ([] : (string * term * term list) list)

    (* val d = el 2 ds *)
    fun process_disj d = let
      val lbl = lbl_gen ()

      (* intro fresh vars *)
      val d_thm = let
        val (evs, d_b) = strip_exists d
        val s = List.map (fn v => (v |-> var_gen (type_of v))) evs
        val evs = List.map (Term.subst s) evs
        val d_b = Term.subst s d_b
        val d' = list_mk_exists (evs, d_b)
        val d_thm = ALPHA d d'
      in
        d_thm
      end

      (* add label *)
      val ld_thm = RIGHT_CONV_RULE (add_labels_CONV [lbl]) d_thm


      (* figure out constructor and free variables and add them
         to list of disjuncts *)
      val _ = let
        val d' = rhs (concl d_thm)
        val (evs, b) = strip_exists d'
        val b_conjs = strip_conj b
        val main_conj = first (fn c' =>
           aconv (lhs c') v handle HOL_ERR _ => false) b_conjs
        val r = rhs main_conj
        val (c, _) = strip_comb_bounded (List.length evs) r
        val _ = disjuncts := (lbl, c, evs) :: !disjuncts
      in () end handle HOL_ERR _ => ()
    in
      ld_thm
    end handle HOL_ERR _ => raise UNCHANGED

    (* val ds = strip_disj (concl nthm) *)
    val nthm' = CONV_RULE (ALL_DISJ_CONV process_disj) nthm
  in
    (nthm', List.rev (!disjuncts))
  end

  fun exists_left_and_label_CONV t = let
    val (lbls_left, _) = (strip_labels o fst o dest_conj o snd o dest_exists) t
    val (lbls_right, _) = (strip_labels o snd o dest_conj o snd o dest_exists) t

    val c_remove = QUANT_CONV (BINOP_CONV (REPEATC markerLib.DEST_LABEL_CONV))

    val thm0 = (c_remove THENC (add_labels_CONV (lbls_left @ lbls_right))) t
  in
    thm0
  end

  fun expand_disjunction_CONV v nthm_expand d_tm = let
    val thm00 = RESORT_EXISTS_CONV (fn vs =>
       let val (v', vs') = pick_element (aconv v) vs in
       (v'::vs') end) d_tm

    val thm01a = HO_PART_MATCH (lhs o snd o strip_forall) nthm_expand (rhs (concl thm00))
    val thm01 = TRANS thm00 thm01a

    val thm02 = RIGHT_CONV_RULE (PURE_REWRITE_CONV [RIGHT_AND_OVER_OR]) thm01
    val thm03 = RIGHT_CONV_RULE (DECEND_CONV BINOP_CONV (TRY_CONV EXISTS_OR_CONV)) thm02

    val thm04 = RIGHT_CONV_RULE (ALL_DISJ_CONV exists_left_and_label_CONV) thm03

    val LEFT_RIGHT_AND_LIST_EXISTS_CONV = (DECEND_CONV QUANT_CONV ((RIGHT_AND_EXISTS_CONV ORELSEC LEFT_AND_EXISTS_CONV)))
    val thm05 = RIGHT_CONV_RULE (ALL_DISJ_CONV (strip_labels_CONV (STRIP_QUANT_CONV LEFT_RIGHT_AND_LIST_EXISTS_CONV))) thm04
    val thm06 = RIGHT_CONV_RULE (ALL_DISJ_CONV (strip_labels_CONV (Unwind.UNWIND_EXISTS_CONV))) thm05
  in
    thm06
  end

  fun expand_cases_in_thm lbl (v, nthm') thm = let
    val nthm_expand = HO_MATCH_MP case_dist_exists_thm (GEN v nthm')

    val thm01 = CONV_RULE (QUANT_CONV (ALL_DISJ_CONV (
       guarded_strip_labels_CONV [lbl] (
       (expand_disjunction_CONV v nthm_expand))))) thm

    val thm02 = CONV_RULE (PURE_REWRITE_CONV [label_over_or_thm, GSYM DISJ_ASSOC]) thm01

   in
     thm02
   end handle HOL_ERR _ => thm


  fun get_columns_for_constructor current_col (c, evs) cols' = let
    fun process_current_col (cs : (term list * term) list list, kl : bool list) ps = case ps of
        [] => (List.map List.rev cs, List.rev kl)
      | (vs, p)::ps' => let
           val (cs', kl') =
             if (Term.is_var p) andalso List.exists (aconv p) vs then
               (Lib.map2 (fn v => fn l => ([v], v)::l) evs cs,
                true::kl)
             else let
               val (c', args) = strip_comb_bounded (List.length evs) p
             in
               if not (aconv c c') then (cs, false::kl) else
               (Lib.map2 (fn a => fn l => (vs, a)::l) args cs,
                true::kl)
             end
         in process_current_col (cs', kl') ps' end

    val ps = (snd current_col)
    val (cs, kl) =  process_current_col (List.map (K []) evs, []) ps
    val cols1 = zip evs cs

    val cols2 = List.map (fn (v, rs) =>
       (v, List.map snd (Lib.filter fst (zip kl rs)))) cols'

    val cols'' = cols1 @ cols2

    (* remove cols consisting of only vars *)
    val cols''' = filter (fn (_, ps) => not (List.all (fn (vs, p) =>    is_var p andalso List.exists (aconv p) vs) ps)) cols''
  in
     cols'''
  end


  (* extract the column for variable v from the list of columns *)
  fun pick_current_column v cols =
    pick_element (fn (v', _) => aconv v v') cols

in (* in of local *)

  fun nchotomy_of_pats_GEN db col_heu pats = let
    val var_gen = mk_var_gen "v" []
    val lbl_gen = mk_new_label_gen "case_"

    (*
      val (thm, cols, lbl) = mk_initial_state var_gen lbl_gen pats
      val (thm, cols, lbl) = (thm1, cols'', lbl)
      val xxx = !args
      val (thm, cols, lbl) = el 3 xxx
*)

    val args = ref []
    fun compile (thm, cols, lbl) = let
      val _ = args := (thm, cols, lbl) :: (!args)
      val (v, nthm) = find_nchotomy_for_cols db col_heu cols
      val (current_col, cols_rest) = pick_current_column v cols
      val (nthm', cases_info) = compute_cases_info var_gen lbl_gen v nthm

      (* Expand all labeled with [lbl] cases *)
      val thm1 = expand_cases_in_thm lbl (v, nthm') thm

      (* Call recursively *)
      val thm2 = let
(*        val ((lbl, c, evs), current_thm) = ((el 2 cases_info, thm1)) *)
        fun process_case ((lbl, c, evs), current_thm) = let
          val cols' = get_columns_for_constructor current_col (c, evs) cols_rest
        in
          compile (current_thm, cols', lbl)
        end
      in
        List.foldl process_case thm1 cases_info
      end
    in
      thm2
    end handle HOL_ERR _ => thm

    (* compile it *)
    val thm3 = compile (mk_initial_state var_gen lbl_gen pats)

    (* get rid of labels *)
    val thm4 = CONV_RULE markerLib.DEST_LABELS_CONV thm3
  in
    thm4
  end

  fun nchotomy_of_pats pats =
      nchotomy_of_pats_GEN (!thePmatchCompileDB) colHeu_default pats

end


(********************************************)
(* Prune disjunctions of PMATCH_ROW_COND_EX *)
(********************************************)

(* Given a list of disjunctions of PMATCH_ROW_COND_EX and
   a theorem stating that a certain PMATCH_ROW_COND_EX does not
   hold, prune the disjunction by removing all patterns
   covered by the one we know does not hold. *)


fun PMATCH_ROW_COND_EX_ELIM_FALSE_GUARD_CONV tt = let
  val (_, _, g) = dest_PMATCH_ROW_COND_EX tt
  val (_, g_b) = pairLib.dest_pabs g
  val _ = if (aconv g_b F) then () else raise UNCHANGED

  val thm00 = PART_MATCH (lhs o rand) PMATCH_ROW_COND_EX_FALSE tt
  val pre = (rand o rator o concl) thm00
  (* set_goal ([], pre) *)
  val pre_thm = prove (pre,
    SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [pairTheory.FORALL_PROD]
  )
  val thm01 = MP thm00 pre_thm
in
  thm01
end handle HOL_ERR _ => raise UNCHANGED


(*
val t = ``
  CASE (x,y,z) OF [
    ||. (NONE,_,[]) ~> 0;
    || x. (NONE,x,[]) when x < 10 ~> x;
    || x. (NONE,x,[2]) ~> x;
    || (x, v18). (NONE,x,[v18]) ~> 3;
    ||. (NONE,_,[_;_]) ~> 4;
    || (x,v12,v16,v17). (NONE,x,v12::v16::v17) ~> 3;
    || (y,x,z,zs). (SOME y,x,[z]) ~> x + 5 + z;
    || (y,v23,v24). (SOME y,0,v23::v24) ~> (v23 + y);
    || (y,z,v23). (SOME y,SUC z,[v23]) when y > 5 ~> 3;
    || (y,z). (SOME y,SUC z,[1; 2]) ~> y + z
  ]``;

  val (v, rows) = dest_PMATCH t
  val pats = List.map (#1 o dest_PMATCH_ROW) rows


val thm = CONV_RULE (nchotomy2PMATCH_ROW_COND_EX_CONV) (nchotomy_of_pats pats)

val cs = (strip_disj o concl o SPEC v) thm

val t  = (concl o SPEC v) thm

val row_cs = List.map (mk_PMATCH_ROW_COND_EX_ROW v) rows

val weaken_ce = el 4 row_cs
val weaken_thm = ASSUME (mk_neg weaken_ce)
val ce = el 4 cs

val rc_arg = ([], NONE)
*)

(* apply thm PMATCH_ROW_COND_EX_WEAKEN *)
fun PMATCH_ROW_COND_EX_WEAKEN_CONV_GENCALL rc_arg (weaken_thm, v_w, p_w', vars_w') ce = let
  val (v, p_t, _) = dest_PMATCH_ROW_COND_EX ce
  val (vars, p) = pairLib.dest_pabs p_t
  val _ = if (aconv v v_w) then () else raise UNCHANGED

  (* try to match *)
  val s = let
    val (s_tm, s_ty) = Term.match_term p_w' p
    val _ = if List.null s_ty then () else failwith "bound too much"
    val vars_w'_l = pairSyntax.strip_pair vars_w'
    val _ = if List.exists (fn s => not (List.exists
        (aconv (#redex s)) vars_w'_l)) s_tm then
         failwith "bound too much" else ()
  in s_tm end

  (* construct f *)
  val f_tm = pairSyntax.mk_pabs (vars, subst s vars_w')

  (* instantiate the thm *)
  val thm0 = let
    val thm00 = FRESH_TY_VARS_RULE PMATCH_ROW_COND_EX_WEAKEN
    val thm01 = MATCH_MP thm00 weaken_thm
    val thm02 = ISPEC f_tm thm01
    val thm03 = PART_MATCH (lhs o rand) thm02 ce
    val thm04 = rc_elim_precond rc_arg thm03
  in
    thm04
  end

  (* Simplify guard *)
  val thm1 = let
       val c = TRY_CONV (rc_conv rc_arg) THENC
               pairTools.PABS_INTRO_CONV vars
     in
       RIGHT_CONV_RULE (RAND_CONV c) thm0
     end

  (* elim false *)
  val thm2 = RIGHT_CONV_RULE
    PMATCH_ROW_COND_EX_ELIM_FALSE_GUARD_CONV thm1
    handle HOL_ERR _ => thm1
in
  thm2
end handle HOL_ERR _ => raise UNCHANGED


fun PMATCH_ROW_COND_EX_DISJ_WEAKEN_CONV_GENCALL rc_arg weaken_thm t = let
  val (v_w, p_tw, _) =
    dest_PMATCH_ROW_COND_EX (dest_neg (concl weaken_thm))
  val (vars_w, p_w) = pairLib.dest_pabs p_tw

  (* get fresh vars in p_w before matching *)
  val (p_w', vars_w') = let
    val vars'_l = pairSyntax.strip_pair vars_w
    val s = List.map (fn v => (v |-> genvar (type_of v)))  vars'_l
    val p_w' = subst s p_w
    val vars_w' = subst s vars_w
  in
    (p_w', vars_w')
  end

  val thm0 = ALL_DISJ_CONV  (PMATCH_ROW_COND_EX_WEAKEN_CONV_GENCALL rc_arg (weaken_thm, v_w, p_w', vars_w')) t


  val thm1 = RIGHT_CONV_RULE (PURE_REWRITE_CONV [boolTheory.OR_CLAUSES]) thm0
in
  thm1
end


(*************************************)
(* Compute redundant rows info for a *)
(* PMATCH                            *)
(*************************************)

(* val tt = el 3 cjs *)

fun SIMPLIFY_PMATCH_ROW_COND_EX_IMP_CONV rc_arg tt = let
  (* destruct everything *)
  val (v, vars', p', g', vars, p, g) = let
    val (pre, cl_neg) = dest_imp tt
    val (v', p', g') = dest_PMATCH_ROW_COND_EX pre
    val (vars', _) = pairSyntax.dest_pabs p'
    val cl = dest_neg cl_neg
    val (v, p, g) = dest_PMATCH_ROW_COND_EX cl
    val _ = if (aconv v v') then () else raise UNCHANGED
    val (vars, _) = pairSyntax.dest_pabs p
  in
    (v, vars', p', g', vars, p, g)
  end

  val thm00 = FRESH_TY_VARS_RULE PMATCH_ROW_COND_EX_IMP_REWRITE
  val thm01 = ISPECL [v, p', g', p, g] thm00

  val thm02 = RIGHT_CONV_RULE (
      (QUANT_CONV (RAND_CONV (pairTools.PABS_INTRO_CONV vars))) THENC
      (RAND_CONV (pairTools.PABS_INTRO_CONV vars'))) thm01
  val thm03 = RIGHT_CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV) thm02
  val thm04 = RIGHT_CONV_RULE (TRY_CONV (pairTools.ELIM_TUPLED_QUANT_CONV) THENC
               TRY_CONV (STRIP_QUANT_CONV (pairTools.ELIM_TUPLED_QUANT_CONV))) thm03

  fun imp_or_no_imp_CONV c t =
    if (is_imp t) then
      (RAND_CONV c) t
    else c t

  val thm05 = RIGHT_CONV_RULE (
      (STRIP_QUANT_CONV (imp_or_no_imp_CONV (RATOR_CONV (RAND_CONV (SIMP_CONV (rc_ss []) []))))) THENC
      REWRITE_CONV[]) thm04

  val rr = rhs (concl thm05)
  val thm06 = if aconv rr T then thm05 else let
      val thm_rr = prove_attempt (rr, rc_tac rc_arg)
    in
      TRANS thm05 (EQT_INTRO thm_rr)
    end handle HOL_ERR _ => thm05
in
  thm06
end

(* val ttts = strip_disj pre
   val ttt = el 1 ttts
   val rc_arg = ([], NONE) *)

fun SIMPLIFY_PMATCH_ROW_COND_EX_IMP_CONV rc_arg cc_thm v ttt = let

  val (v', p, g) = dest_PMATCH_ROW_COND_EX ttt
  val _ = if (aconv v v') then () else raise UNCHANGED

  val thm00 = FRESH_TY_VARS_RULE PMATCH_ROW_COND_EX_IMP_REWRITE
  val thm01 = MATCH_MP thm00 cc_thm
  val thm02 = ISPECL [p, g] thm01

  val (x, pre, l) = let
     val (x, body) = (dest_forall o rand o rator o snd o strip_forall o concl) thm02
     val (pre, body') = dest_imp body
     val l = lhs body'
  in
    (x, pre, l)
  end

  val l_thm0 = rc_conv_rws rc_arg [ASSUME pre] l
  val r = rhs (concl l_thm0)
  val _ = if (aconv r T) orelse (aconv r F) then () else
          (* we don't want complicated intermediate results *)
          raise UNCHANGED
  val l_thm1 = GEN x (DISCH pre l_thm0)

  val thm03 = ISPEC r thm02
  val thm04 = MP thm03 l_thm1
in
  thm04
end


(* val thm = it
   val (tts, _) = (listSyntax.dest_list o rand o concl) thm
   val tt = el 2 tts *)

val simple_imp_thm  = prove ( ``!X Y X'. ((Y ==> (X = X')) ==> ((X ==> ~Y) = (X' ==> ~Y)))``,
PROVE_TAC[])

fun SIMPLIFY_REDUNDANT_ROWS_INFO_AUX rc_arg tt = let
  val (pre, cc_neg) = dest_imp tt
  val cc = dest_neg cc_neg

  val (v, _, _) = dest_PMATCH_ROW_COND_EX cc
  val cc_thm = ASSUME cc
  val pre_thm0 =
    (ALL_DISJ_TF_ELIM_CONV (SIMPLIFY_PMATCH_ROW_COND_EX_IMP_CONV rc_arg cc_thm v)) pre handle UNCHANGED => REFL pre
  val pre_thm = DISCH cc pre_thm0

  val thm0 = SPECL [pre, cc] simple_imp_thm
  val thm1 = MATCH_MP thm0 pre_thm

  val thm2 = RIGHT_CONV_RULE (REWRITE_CONV [] THENC DEPTH_CONV
    PMATCH_ROW_COND_EX_ELIM_CONV) thm1
in
  thm2
end handle HOL_ERR _ => raise UNCHANGED


fun find_non_constructor_pattern db vs t = let
  fun aux l = case l of
      [] => NONE
    | (t::ts) =>  if (mem t vs) then aux ts else (
        if (pairSyntax.is_pair t) then
          aux ((pairSyntax.strip_pair t)@ts)
        else (
          case pmatch_compile_db_dest_constr_term db t of
             NONE => SOME t
           | SOME (_, args) => aux ((map snd args) @ ts)
        )
      )
in
  aux [t]
end


fun COMPUTE_REDUNDANT_ROWS_INFO_OF_PMATCH_GENCALL rc_arg db col_heu t =
let
  val (v, rows) = dest_PMATCH t
  val rc_arg = case rc_arg of
    (sl, cb_opt) => ((#pcdb_ss db)::sl, cb_opt)


  (* compute initial enchotomy *)
  val nchot_thm = let
    val pats = List.map (#1 o dest_PMATCH_ROW) rows
    val thm01 = nchotomy_of_pats_GEN db col_heu pats
    val thm02 = CONV_RULE (nchotomy2PMATCH_ROW_COND_EX_CONV_GEN
       (find_non_constructor_pattern db)
    ) thm01
    val thm03 = ISPEC v thm02
  in
    thm03
  end

  (* get initial info *)
  val init_info = let
    val row_ty = listSyntax.dest_list_type (type_of (rand t))
    val s_ty = match_type (``:'a -> 'b option``) row_ty
    val thm00 = INST_TYPE s_ty IS_REDUNDANT_ROWS_INFO_NIL
    val thm01 = SPEC v thm00

    val nthm = GSYM (EQT_INTRO nchot_thm)
    val thm02 = CONV_RULE (RATOR_CONV (RAND_CONV (K nthm))) thm01
  in
    thm02
  end

  (* add a row to the info *)
  fun add_row (r, info_thm) = let
     val (p, g, r) = dest_PMATCH_ROW r
     val thm00 = FRESH_TY_VARS_RULE IS_REDUNDANT_ROWS_INFO_SNOC_PMATCH_ROW
     val thm01 = MATCH_MP thm00 info_thm
     val thm02 = ISPECL [p, g, r] thm01

     (* simplify the condition we carry around *)
     val c'_thm = let
       val pthm = ASSUME (mk_neg (mk_PMATCH_ROW_COND_EX (v, p, g)))
       val c_tm = (rand o rator o concl) info_thm
       val c'_thm0 = PMATCH_ROW_COND_EX_DISJ_WEAKEN_CONV_GENCALL rc_arg pthm c_tm handle UNCHANGED => REFL c_tm
       val c'_thm = DISCH (concl pthm) c'_thm0
     in
       c'_thm
     end

     val thm03 = MATCH_MP thm02 c'_thm
     val thm04 = CONV_RULE (RATOR_CONV (RATOR_CONV (RAND_CONV listLib.SNOC_CONV))) thm03

     val new_cond_CONV = SIMPLIFY_REDUNDANT_ROWS_INFO_AUX rc_arg
     val thm05 = CONV_RULE (RAND_CONV (RATOR_CONV (RAND_CONV new_cond_CONV))) thm04

     val thm06 = CONV_RULE (RAND_CONV (listLib.SNOC_CONV)) thm05
  in
     thm06
  end
in
  List.foldl add_row init_info rows
end

fun COMPUTE_REDUNDANT_ROWS_INFO_OF_PMATCH_GEN ss db col_heu =
  COMPUTE_REDUNDANT_ROWS_INFO_OF_PMATCH_GENCALL (ss, NONE) db col_heu

fun COMPUTE_REDUNDANT_ROWS_INFO_OF_PMATCH t =
  COMPUTE_REDUNDANT_ROWS_INFO_OF_PMATCH_GENCALL ([], NONE)
    (!thePmatchCompileDB) colHeu_default t


(*
val t = ``CASE (x, z) OF [
  ||. (NONE, NONE) ~> 0;
  ||. (SOME _, _) ~> 1;
  ||. (_, SOME _) ~> 2
]``

val t = ``CASE (x, z) OF [
  ||. (NONE, NONE) ~> 0;
  ||. (SOME _, _) ~> 1;
  ||. (_, NONE) ~> 2
]``

val t = ``CASE (x, z) OF [
  ||. (NONE, 1) ~> 0;
  ||. (SOME _, 2) ~> 1;
  || x. (_, x) when x > 5 ~> 2
]``
*)

fun IS_REDUNDANT_ROWS_INFO_WEAKEN_RULE info_thm = let
  val (conds, _) = listSyntax.dest_list (rand (concl info_thm))
  val conds' = List.map (fn c => if (aconv c T) then T else F) conds
  val conds'_tm = listSyntax.mk_list (conds', bool)

  val thm00 = REDUNDANT_ROWS_INFOS_CONJ_THM
  val thm01 = MATCH_MP thm00 info_thm
  val thm02 = SPECL [F, conds'_tm] thm01

  val thm03 = let
    val pre = rand (rator (concl thm02))
    val pre_thm = prove (pre, SIMP_TAC list_ss [])
  in
    MP thm02 pre_thm
  end

  val thm04 = CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV []))) thm03

  val thm05 = CONV_RULE (RAND_CONV (REWRITE_CONV [
    REDUNDANT_ROWS_INFOS_CONJ_REWRITE])) thm04
in
  thm05
end

fun IS_REDUNDANT_ROWS_INFO_TO_PMATCH_EQ_THM info_thm = let
  val info_thm' = IS_REDUNDANT_ROWS_INFO_WEAKEN_RULE info_thm
  val thm0 = MATCH_MP REDUNDANT_ROWS_INFO_TO_PMATCH_EQ info_thm'
  val c = PURE_REWRITE_CONV [APPLY_REDUNDANT_ROWS_INFO_THMS]
  val thm1 = RIGHT_CONV_RULE (RAND_CONV c) thm0
in
  thm1
end


fun PMATCH_REMOVE_REDUNDANT_CONV_GENCALL db col_heu rc_arg t = let
  val info_thm = COMPUTE_REDUNDANT_ROWS_INFO_OF_PMATCH_GENCALL rc_arg db col_heu t
in
  IS_REDUNDANT_ROWS_INFO_TO_PMATCH_EQ_THM info_thm
end

fun PMATCH_REMOVE_REDUNDANT_CONV_GEN db col_heu ssl =
  PMATCH_REMOVE_REDUNDANT_CONV_GENCALL db col_heu (ssl, NONE)

fun PMATCH_REMOVE_REDUNDANT_CONV t = PMATCH_REMOVE_REDUNDANT_CONV_GEN
  (!thePmatchCompileDB) colHeu_default [] t;

fun PMATCH_REMOVE_REDUNDANT_GEN_ss db col_heu ssl =
  make_gen_conv_ss (PMATCH_REMOVE_REDUNDANT_CONV_GENCALL db col_heu)  "PMATCH_REMOVE_REDUNDANT_REDUCER" ssl

fun PMATCH_REMOVE_REDUNDANT_ss () =
  PMATCH_REMOVE_REDUNDANT_GEN_ss (!thePmatchCompileDB) colHeu_default []


fun IS_REDUNDANT_ROWS_INFO_SHOW_ROW_IS_REDUNDANT thm i tac =
  CONV_RULE (RAND_CONV (list_nth_CONV i (fn t =>
    EQT_INTRO (prove (t, tac))))) thm

fun IS_REDUNDANT_ROWS_INFO_SHOW_ROW_IS_REDUNDANT_set_goal thm i = let
  val (l, _) = (listSyntax.dest_list o rand o concl) thm
  val t = List.nth (l, i)
in
  Manager.set_goal ([], t)
end


(*************************************)
(* Exhaustiveness                    *)
(*************************************)

(*
val db = !thePmatchCompileDB
val col_heu = colHeu_default
val rc_arg = ([], NONE)
*)


(*
val t = ``CASE (x, z) OF [
  ||. (NONE, NONE) ~> 0;
  ||. (_, SOME _) ~> 2
]``

val t = ``CASE (x, z) OF [
  ||. (NONE, NONE) ~> 0;
  ||. (SOME _, _) ~> 1;
  ||. (_, NONE) ~> 2
]``

val t = ``CASE (x, z) OF [
  ||. (NONE, 1) ~> 0;
  ||. (SOME _, 2) ~> 1;
  || x. (_, x) when x > 5 ~> 2
]``

val info_thm = COMPUTE_REDUNDANT_ROWS_INFO_OF_PMATCH t

*)


fun IS_REDUNDANT_ROWS_INFO_TO_PMATCH_IS_EXHAUSTIVE info_thm = let
  val thm0 = MATCH_MP IS_REDUNDANT_ROWS_INFO_EXTRACT_IS_EXHAUSTIVE
    info_thm
in
  thm0
end


fun PMATCH_IS_EXHAUSTIVE_CONSEQ_CONV_GEN db col_heu ssl t = let
  val info_thm = COMPUTE_REDUNDANT_ROWS_INFO_OF_PMATCH_GENCALL (ssl, NONE) db col_heu t
in
  IS_REDUNDANT_ROWS_INFO_TO_PMATCH_IS_EXHAUSTIVE info_thm
end

fun PMATCH_IS_EXHAUSTIVE_CONSEQ_CONV t =
  PMATCH_IS_EXHAUSTIVE_CONSEQ_CONV_GEN
  (!thePmatchCompileDB) colHeu_default [] t;




(*************************************)
(* Nchotomy                          *)
(*************************************)

(*
val db = !thePmatchCompileDB
val col_heu = colHeu_default
val rc_arg = ([], NONE)
*)


val neg_imp_rewr = prove (``(~A ==> B) = (~B ==> A)``,
  Cases_on `A` THEN   Cases_on `B` THEN REWRITE_TAC[]);

fun nchotomy_PMATCH_ROW_COND_EX_CONSEQ_CONV_GEN rc_arg db col_heu tt = let
  (* destruct everything *)
  val (v, disjs) = let
    val disjs = strip_disj tt
    val (v, _, _) = dest_PMATCH_ROW_COND_EX (hd disjs)
  in
    (v, disjs)
  end

  (* Sanity check *)
  val _ = List.map (fn r => let
    val (v', _, _) = dest_PMATCH_ROW_COND_EX r
    val _ = if (aconv v v') then () else failwith "illformed input"
  in () end) disjs

  (* derive nchot thm *)
  val nchot_thm = let
    val pats = List.map (#2 o dest_PMATCH_ROW_COND_EX) disjs
    val thm01 = nchotomy_of_pats_GEN db col_heu pats
    val thm02 = CONV_RULE (nchotomy2PMATCH_ROW_COND_EX_CONV_GEN
      (find_non_constructor_pattern db)) thm01
    val thm03 = ISPEC v thm02
  in
    thm03
  end

  (* prepare assumptions *)
  val neg_tt = mk_neg tt
  val pre_thms = let
     val thm00 = ASSUME neg_tt
     val thm01 = PURE_REWRITE_RULE [DE_MORGAN_THM] thm00
   in BODY_CONJUNCTS thm01 end


  (* apply these assumptions to the nchot_thm *)
  val nchot_thm' = let
    fun step (pre_thm, thm) =
      CONV_RULE (PMATCH_ROW_COND_EX_DISJ_WEAKEN_CONV_GENCALL rc_arg pre_thm) thm
    val thm00 = foldl step nchot_thm pre_thms
    val thm01 = DISCH neg_tt thm00
    in
      thm01
    end

  val nchot_thm'' = let
    val thm00 = CONV_RULE (REWR_CONV neg_imp_rewr) nchot_thm'
    val thm01 = CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV []))) thm00
  in thm01 end

in
  nchot_thm''
end


fun SHOW_NCHOTOMY_CONSEQ_CONV_GEN ssl db col_heu tt = let
  val (x, b) = dest_forall tt
  val b_thm = ALL_DISJ_CONV (PMATCH_ROW_COND_EX_INTRO_CONV_GEN
    (find_non_constructor_pattern db) x) b

  val thm2 = nchotomy_PMATCH_ROW_COND_EX_CONSEQ_CONV_GEN (ssl, NONE) db col_heu (rhs (concl b_thm))

  val thm3 = CONV_RULE (RAND_CONV (K (GSYM b_thm))) thm2

  val thm4 = CONV_RULE (RATOR_CONV (RAND_CONV (DEPTH_CONV (PMATCH_ROW_COND_EX_ELIM_CONV)))) thm3

  val thm5 = GEN x thm4
in
  thm5
end

fun SHOW_NCHOTOMY_CONSEQ_CONV tt =
  SHOW_NCHOTOMY_CONSEQ_CONV_GEN [] (!thePmatchCompileDB) colHeu_default tt



(*************************************)
(* Add missing patterns              *)
(*************************************)

(*
val use_guards = true
val rc_arg = ([], NONE)
val db = !thePmatchCompileDB
val col_heu = colHeu_default
*)

fun PMATCH_COMPLETE_CONV_GENCALL rc_arg db col_heu use_guards t = let
  val (v, rows) = dest_PMATCH t
  fun row_to_cond_ex r = let
    val (vs_t, p, g, _) = dest_PMATCH_ROW_ABS r
    val vs = pairSyntax.strip_pair vs_t
  in
    mk_PMATCH_ROW_COND_EX_PABS_MOVE_TO_GUARDS (find_non_constructor_pattern db) vs (v, p, g)
  end
  val disjs = List.map row_to_cond_ex rows
  val disjs_tm = list_mk_disj disjs

  val thm_nchot = nchotomy_PMATCH_ROW_COND_EX_CONSEQ_CONV_GEN rc_arg db col_heu disjs_tm

  val missing_list = let
    val pre = fst (dest_imp (concl thm_nchot))
    val disj = dest_neg pre
  in
    strip_disj disj
  end handle HOL_ERR _ => raise UNCHANGED

  fun add_missing_pat (missing_t, thm) = let
    val (_, vs, p_t0, g_t0) = dest_PMATCH_ROW_COND_EX_ABS missing_t
    val g_t1 = if use_guards then g_t0 else T
    val g_t = pairSyntax.mk_pabs (vs, g_t1)
    val p_t = pairSyntax.mk_pabs (vs, p_t0)
    val r_t = pairSyntax.mk_pabs (vs, mk_arb (type_of t))

    val thm00 = FRESH_TY_VARS_RULE PMATCH_REMOVE_ARB
    val rows_t = (rand o rhs o concl) thm
    val thm01 = ISPECL [p_t, g_t, r_t, v, rows_t] thm00
    val thm02 = rc_elim_precond rc_arg thm01
    val thm03 = GSYM thm02
    val thm04 = RIGHT_CONV_RULE (RAND_CONV (listLib.SNOC_CONV)) thm03
  in
    TRANS thm thm04
  end

in
  foldl add_missing_pat (REFL t) missing_list
end

fun PMATCH_COMPLETE_CONV_GEN ssl =
    PMATCH_COMPLETE_CONV_GENCALL (ssl, NONE);

val PMATCH_COMPLETE_CONV =
    PMATCH_COMPLETE_CONV_GEN [] (!thePmatchCompileDB) colHeu_default;

fun PMATCH_COMPLETE_GEN_ss ssl db colHeu use_guards =
  make_gen_conv_ss (fn rc_arg =>
    PMATCH_COMPLETE_CONV_GENCALL rc_arg db colHeu use_guards)
    "PMATCH_COMPLETE_REDUCER" ssl;

val PMATCH_COMPLETE_ss = PMATCH_COMPLETE_GEN_ss [] (!thePmatchCompileDB) colHeu_default;


(*


val tt = rhs (concl thm)
val x = el 2 (free_vars tt)
val tt = mk_forall(v, tt)

val thm = DEPTH_CONV (PMATCH_ROW_COND_EX_ELIM_CONV) tt

val t = dest_forall ``!x y. XXX``
val t = ``PMATCH (x,z) [
  ||. (NONE, c) ~> 0
]``

val t = ``PMATCH (x, z) [
  ||. (NONE, c) ~> 0;
  ||. (SOME _, _) ~> 1;
  ||. (_, NONE) ~> 2
]``

val (v, rows) = dest_PMATCH t
fun mk_xx r = let
  val (p, g, _) = dest_PMATCH_ROW r
in
  mk_PMATCH_ROW_COND_EX (v, p, g)
end
val disjs = List.map mk_xx rows
val disjs_tm = list_mk_disj disjs
val tt = list_mk_disj disjs
*)


end
