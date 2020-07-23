structure patternMatchesLib :> patternMatchesLib =
struct

open HolKernel Parse boolLib Drule BasicProvers
open simpLib numLib metisLib
open patternMatchesTheory
open listTheory
open quantHeuristicsLib
open DatatypeSimps
open patternMatchesSyntax
open Traverse
open constrFamiliesLib
open unwindLib
open oneSyntax

structure Parse =
struct
  open Parse
  val (Type,Term) =
      parse_from_grammars patternMatchesTheory.patternMatches_grammars
end
open Parse

val std_ss   = std_ss -* ["lift_disj_eq", "lift_imp_disj"]
val list_ss  =
    numLib.arith_ss ++ listSimps.LIST_ss -* ["lift_disj_eq", "lift_imp_disj"]

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

(* Often in the following, a single row needs extracting.
   given a list l, we want to an element [n], the list of
   elements before it and the list of elements after it.
   So, we need an efficient way to compute:
   (List.take (l, n), List.nth (l, n), List.drop (l, n+1))

   extract_element [0,1,2,3,4,5] 0  = ([], 0, [1,2,3,4,5])
   extract_element [0,1,2,3,4,5] 1  = ([0], 1, [2,3,4,5])
   extract_element [0,1,2,3,4,5] 3  = ([0,1,2], 3, [4,5])
   extract_element [0,1,2,3,4,5] 5  = ([0,1,2,3,4], 5, [])
 *)

fun extract_element l n = let
  val (l1, l2) = Lib.split_after n l
  in
    case l2 of
        [] => failwith "index too large"
      | x::xs => (l1, x, xs)
  end


(* Similarly, we often need to replace an element with
   a list of elements. We need an efficient way to compute

   (List.take (l, n) @ new_elements @ List.drop (l, n+1),
    List.nth (l, n))
 *)
fun replace_element l n new =
  if n < 0 then failwith "index too small"
  else let
    fun aux _ (_, []) = failwith "index too big"
      | aux 0 (acc, x::xs) =
          (List.revAppend (acc, new @ xs), x)
      | aux n (acc, x::xs) =
          aux (n-1) (x::acc, xs)
  in
     aux n ([], l)
  end

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
  STRUCT_CASES_TAC (SPEC ``x:'a#'b`` pairTheory.pair_CASES) THEN
  SIMP_TAC std_ss []);

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
   quantHeuristicsLib.SIMPLE_QUANT_INST_ss,
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
fun rc_ss gl =
    simpLib.remove_ssfrags
      ["patternMatchesSimp"]
      (srw_ss() ++ simpLib.merge_ss (static_ss :: gl) -*
       ["lift_disj_eq", "lift_imp_disj"])

(* finally we add a call-back component. This is an
   external conversion that is used at the end if
   everything else fails. This is used to have nested calls
   of the simplifier. The simplifier executes some conversion that
   uses rs_ss. At the end, we might want to use the external
   simplifier. This is realised with these call-backs. *)
fun callback_CONV cb_opt t = (case cb_opt of
    NONE => NO_CONV t
  | SOME cb => (if (can (find_term is_PMATCH) t) then
                  NO_CONV t
                else cb t));

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
  val _ = if is_var a andalso free_in a x then () else failwith "case-split on non pattern var"
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

  (* compile patterns *)
  val case_tm0 = GrammarSpecials.compile_pattern_match rows_tm


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

val t = ``
   case l of
     | [] => 0
     | x::y::x::y::_ => (x + y)
     | x::x::x::x::_ when (x > 10) => x
     | x::x::x::x::x::_ => 9
     | [] => 1
     | x::x::x::y::_ => (x + x + x)
     | x::_ => 1
     | x::y::z::_ => (x + x + x)
   ``

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
    val vars' = map (fn x => #residue x) s
    val pb' = subst s pb
  in
    (vars', pb')
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
     fun does_match ((_, (v1, p1)), (_, (v2, p2))) =
     let
        val (t_s, ty_s) = match_term p1 p2
     in
        null ty_s andalso Lib.all (fn x => tmem (#redex x) v1) t_s
     end handle HOL_ERR _ => false
  in
     List.filter does_match candidates
  end

  (* filtering finished, now try it for real *)
  val cands = List.map (fn ((p1, _), (p2, _)) => (p1, p2)) candidates_match
  (* val (r_no1, r_no2) = el 1 cands *)
  fun try_pair (r_no1, r_no2) = let
    val tm0 = let
      val (rows1, r1, rows_rest) = extract_element rows r_no1
      val (rows2, r2, rows3) = extract_element rows_rest (r_no2 - r_no1 - 1)

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
   ``case (x,y,z) of
    | (0,v1) => 2
    | (SUC v4,NONE,[]) => (SUC v4)
    | (SUC v4,NONE,v10::v11) => ARB
    | (v4,NONE,_) => v4
    | (0,SOME _ ,_) => ARB
    | (SUC v4,SOME v9,v8) => (SUC v4 + v9)
  ``

*)

(* When removing subsumed rows, i.e. rows that can be dropped,
   because a following rule covers them, we can sometimes drop rows with
   right-hand-side ARB, because PMATCH v [] evalutates to ARB.
   This is semantically fine, but changes the users-view. The resulting
   case expression might e.g. not be exhaustive any more. This can
   also cause trouble for code generation. Therefore the parameter
   [exploit_match_exp] determines, whether this optimisation is performed. *)
fun PMATCH_REMOVE_FAST_SUBSUMED_CONV_GENCALL_SINGLE
  exploit_match_exp rc_arg t = let
  val (v, rows) = dest_PMATCH t
  val candidates = compute_row_pat_pairs rows

  (* quick filter on matching *)
  val candidates_match = let
     fun does_match ((_, (v1, p1)), (_, (v2, p2))) =
     let
        val (t_s, ty_s) = match_term p2 p1
     in
        (null ty_s) andalso
        (Lib.all (fn x => tmem (#redex x) v2) t_s)
     end handle HOL_ERR _ => false
  in
     List.filter does_match candidates
  end

  val cands_sub = List.map (fn ((p1, _), (p2, _)) => (p1, SOME p2)) candidates_match

  (* filtering finished, now try it for real *)
  fun cands_arb () = Lib.mapfilter (fn (i, r) => let
     val (_, _, _, r) = dest_PMATCH_ROW_ABS r in
   (dest_arb r; (i, (NONE : int option))) end) (Lib.enumerate 0 rows)

  val cands = if exploit_match_exp then (cands_sub @ cands_arb ()) else
    cands_sub

  (* filtering finished, now try it for real *)
  (* val (r_no1, r_no2_opt) = el 2 cands_arb *)
  fun try_pair (r_no1, r_no2_opt) = let
    fun mk_row_list rs = listSyntax.mk_list (rs, type_of (hd rows))

    fun extract_el_n n rs = let
      val (rows1,r1,rows_rest) = extract_element rs n
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

fun PMATCH_REMOVE_FAST_SUBSUMED_CONV_GENCALL eme rc_arg = REPEATC (PMATCH_REMOVE_FAST_SUBSUMED_CONV_GENCALL_SINGLE eme rc_arg)
fun PMATCH_REMOVE_FAST_SUBSUMED_CONV_GEN eme ssl = PMATCH_REMOVE_FAST_SUBSUMED_CONV_GENCALL eme (ssl, NONE)
fun PMATCH_REMOVE_FAST_SUBSUMED_CONV eme = PMATCH_REMOVE_FAST_SUBSUMED_CONV_GEN eme []


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
     val _ = if (type_of vars_tm = one_ty) then raise UNCHANGED else ()
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

val t = ``case (SUC x) of x => x + 3``

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
  val _ = if (null rows) then raise UNCHANGED else ()

  fun check_row r = let
    val r_tm = mk_eq (mk_comb (r, v), optionSyntax.mk_none (type_of t))
    val r_thm = rc_conv rc_arg r_tm
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

  val _ = if ((check_row_exists true rows_checked_rev) orelse (check_row_exists false (tl rows_checked_rev)) orelse (check_row_exists false [hd rows_checked])) then () else raise UNCHANGED

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
           val thmA = FRESH_TY_VARS_RULE PMATCH_EXTEND_OLD
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
fun PMATCH_CLEANUP_GEN_ss ssl =
  make_gen_conv_ss PMATCH_CLEANUP_CONV_GENCALL "PMATCH_CLEANUP_REDUCER" ssl
val PMATCH_CLEANUP_ss = PMATCH_CLEANUP_GEN_ss []
val PMATCH_CLEANUP_CONV = PMATCH_CLEANUP_CONV_GEN [];
val _ = computeLib.add_convs [(patternMatchesSyntax.PMATCH_tm, 2, QCHANGED_CONV PMATCH_CLEANUP_CONV)];


(***********************************************)
(* simplify a column                           *)
(***********************************************)

(* This can also be considered partial evaluation *)

fun pair_get_col col v = let
  val vs = pairSyntax.strip_pair v
  val (vs', c_v) = replace_element vs col []
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
    [PMATCH_ROW (\x. (x,[])) (\x. T) (\x. x);
     PMATCH_ROW (\ (x,y,ys). (x,y::ys)) (\ (x,y,ys). T)
       (\ (x,y,ys). my_d (x + y,ys))]``


val t = ``PMATCH (x,y)
    [PMATCH_ROW (\x. (x,x)) (\x. T) (\x. T);
     PMATCH_ROW (\ (z, y). (z, y)) (\ (z, y). T) (\ (z, y). F)]``


val rc_arg = []
val col = 0
*)

fun PMATCH_REMOVE_COL_AUX rc_arg col t = let
  val (v, rows) = dest_PMATCH t
  val (v', c_v) = pair_get_col col v
  val vs = free_vars c_v

  val thm_row = let
    val thm = FRESH_TY_VARS_RULE PMATCH_ROW_REMOVE_FUN_VAR
    val thm = ISPEC v thm
    val thm = ISPEC v' thm
  in thm end

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
             val (vars', _) = replace_element vars pv_i []
           in
             if (List.null vars') then [variant avoid ``_uv:unit``] else vars'
           end

           val vars'_tm = pairSyntax.list_mk_pair vars'
           val g' = let
             val (vs, _) = replace_element vars pv_i [c_v]
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
           val vars' = if (List.null vars') then [variant avoid ``_uv:unit``] else vars'
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
       val thm = thm_row
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

    val (vars, _) = replace_element vs_vars col args_vars
    val (ff_res, _) = replace_element vs_vars col [list_mk_comb (c, args_vars)]
    val ff_tm = pairSyntax.mk_pabs (pairSyntax.list_mk_pair vars,
       pairSyntax.list_mk_pair ff_res)

    fun ff_inv tt = let
      val tts = pairSyntax.strip_pair tt
      val tt_args = List.nth(tts, col)

      val (c', args') = strip_comb tt_args
      val _ = if (aconv c c') then () else failwith "different constr"

      val (vars,_) = replace_element tts col args'
    in
      pairSyntax.list_mk_pair vars
    end

    fun ff_inv_var avoid tt = let
      val tts = pairSyntax.strip_pair tt
      val tt_col = List.nth(tts, col)

      val _ = if (is_var tt_col) then () else failwith "no var"

      val (var_basename, _) = dest_var (tt_col)
      val gen_fun = mk_var_gen (var_basename ^ "_") avoid;
      val args =  map (fn t => gen_fun (type_of t)) args_vars

      val (vars, _) = replace_element tts col args
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

  val thm_row = let
     val thm = FRESH_TY_VARS_RULE PMATCH_ROW_REMOVE_FUN_VAR
     val thm = ISPEC v thm
     val thm = ISPEC v' thm
  in thm end

  fun PMATCH_ROW_REMOVE_VAR_COL_AUX row = let
     val (vars_tm, pt, gt, rh) = dest_PMATCH_ROW_ABS row
     val vars = pairSyntax.strip_pair vars_tm

     val avoid = vars @ free_vars pt @ free_vars rh @ free_vars gt
     val (pt', pv, new_vars) = ff_inv_var avoid pt

     val pv_i = index (aconv pv) vars

     val vars' = let
       val (vars', _) = replace_element vars pv_i new_vars
     in
       if (List.null vars') then [variant avoid ``_uv:unit``] else vars'
     end

     val vars'_tm = pairSyntax.list_mk_pair vars'
     val f_tm = let
        val c_v = list_mk_comb (c, new_vars)
        val (vs, _) = replace_element vars pv_i [c_v]
        val vs_tm = pairSyntax.list_mk_pair vs
     in
        pairSyntax.mk_pabs (vars'_tm, vs_tm)
     end

     val vpt = pairSyntax.mk_pabs (vars_tm, pt)
     val vpt' = pairSyntax.mk_pabs (vars'_tm, pt')
     val vrh = pairSyntax.mk_pabs (vars_tm, rh)
     val vgt = pairSyntax.mk_pabs (vars_tm, gt)

     val thm0 = let
       val thm = ISPEC f_tm thm_row
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
val PMATCH_SIMP_COLS_CONV = PMATCH_SIMP_COLS_CONV_GEN [];


(***********************************************)
(* Resort and add dummy columns                *)
(***********************************************)

(*
val t = ``PMATCH (s:'a option,x : 'a option, l:num list)
     [PMATCH_ROW (\_uv:unit. (NONE,NONE,[])) (\_uv. T) (\_uv. NONE);
      PMATCH_ROW (\z. (NONE,z,[2])) (\z. F) (\z. z);
      PMATCH_ROW (\(x, b). (SOME b,x,[2])) (\(x, b). T) (\(x, b). x);
      PMATCH_ROW (\(_0,y). (y,_0,[2])) (\(_0, y). IS_SOME y) (\(_0, y). y)
   ]``

val nv = ``((l:num list), x : 'a option, xx:'a, s:'a option, z:'b)``

val t = ``case (xs : num list) of [] => x | _ => HD xs``
val t = ``case (xs : num list) of [] => x | _::_ => HD xs``
val nv = ``(xs: num list, x:num)``
val rc_arg = ([], NONE)

*)
fun PMATCH_EXTEND_INPUT_CONV_GENCALL rc_arg nv t = let
  val (v, rows) = dest_PMATCH t
  val _ = if aconv v nv then raise UNCHANGED else ()

  val (new_pat_tm, new_col_vars, new_col_subst, old_col_vars, f'_tm, nv_vars_pair) = let
    val nv_parts = pairSyntax.strip_pair nv
    val v_parts = pairSyntax.strip_pair v
    val v_l = map (fn t => (t, genvar (type_of t))) v_parts

    val avoid = all_varsl [t, nv]
    val gen_fun = mk_var_gen "_" avoid

    fun compute_nv_l res_l nv_vars v_l [] =
      if (null v_l) then (res_l, nv_vars) else failwith "PMATCH_EXTEND_INPUT_CONV_AUX: part missing"

    | compute_nv_l res nv_vars v_l (p::nv_parts) = let
        val ((_, v_v), v_l') = pluck (fn (t, _) => aconv p t) v_l
      in
        compute_nv_l (v_v::res) nv_vars v_l' nv_parts
      end handle HOL_ERR _ => let
        val vg = gen_fun (type_of p)
      in
        compute_nv_l (vg::res) (vg::nv_vars) v_l nv_parts
      end

    val (res_l, nv_vars) = compute_nv_l [] [] v_l nv_parts

    val t0 = pairSyntax.list_mk_pair (List.rev res_l)

    val nv_parts_vars = filter (fn (v, n) => is_var n) (zip (List.rev res_l) nv_parts)
    val t1 = pairSyntax.list_mk_pair (map fst nv_parts_vars)
    val f'_tm = pairSyntax.mk_pabs(t0, t1)
    val nv_vars_pair = pairSyntax.list_mk_pair (map snd nv_parts_vars)
    val nv_parts_subst = map (fn (v, n) => v |-> n) nv_parts_vars
  in
    (t0, List.rev nv_vars, nv_parts_subst, List.map snd v_l, f'_tm, nv_vars_pair)
  end

  val thm_row = let
    val thm = FRESH_TY_VARS_RULE PMATCH_ROW_EXTEND_INPUT
    val thm = ISPEC v thm
    val thm = ISPEC nv thm
    val thm = ISPEC f'_tm thm
  in thm end

  fun process_row_aux row = let
     val (pt, gt, rh) = dest_PMATCH_ROW row
     val (vars_tm, pt_b) = pairSyntax.dest_pabs pt

     val (old_vars_tm, new_vars) =
        if ((type_of vars_tm) = one_ty) then (
          if (List.null new_col_vars) then
            (one_tm, [vars_tm])
          else (one_tm, new_col_vars)
        ) else (
          let val ov = pairSyntax.strip_pair vars_tm
          in (vars_tm, ov @ new_col_vars) end
        )

     val pat_vars_s0 = let
         val pt_ps = pairSyntax.strip_pair pt_b
       in map2 (fn v => fn t => (v |-> t)) old_col_vars pt_ps end

     val new_vars_s0 = filter (fn vp => free_in (#residue vp) row
       andalso is_var (subst pat_vars_s0 (#redex vp))) new_col_subst

     val new_vars_s = map (fn vp => subst pat_vars_s0 (#redex vp) |-> #residue vp) new_vars_s0
     val pat_vars_s = map (fn vp => #redex vp |-> subst new_vars_s (#residue vp)) pat_vars_s0

     val new_vars_tm = subst new_vars_s (pairSyntax.list_mk_pair new_vars)
     val pt_b' = subst pat_vars_s (subst new_vars_s new_pat_tm)

     val f_tm = pairSyntax.mk_pabs (new_vars_tm, subst new_vars_s old_vars_tm)
     val pt' = pairSyntax.mk_pabs (new_vars_tm, pt_b')

     val thm0 = let
       val thm = ISPEC f_tm thm_row
       val thm = ISPEC pt thm
       val thm = ISPEC (pairSyntax.mk_pabs (nv_vars_pair, gt)) thm
       val thm = ISPEC (pairSyntax.mk_pabs (nv_vars_pair, rh)) thm
       val thm = ISPEC pt' thm

       fun elim_conv_aux vs = (
         (pairTools.PABS_INTRO_CONV vs) THENC
         (DEPTH_CONV (pairLib.PAIRED_BETA_CONV ORELSEC BETA_CONV))
       )

       fun elim_conv vs = PMATCH_ROW_ARGS_CONV (elim_conv_aux vs)
       val thm = CONV_RULE ((RAND_CONV o RHS_CONV) (elim_conv new_vars_tm)) thm
     in
       thm
     end

     val pre_tm = fst (dest_imp (concl thm0))
(* set_goal ([], pre_tm) *)
     val pre_thm = prove (pre_tm, rc_tac rc_arg)
     val thm1 = MP thm0 pre_thm

     val eq_tm = mk_eq (mk_comb (row, v), lhs (concl thm1))
     val eq_thm = prove (eq_tm, SIMP_TAC std_ss [])
     val thm2 = TRANS eq_thm thm1

     (* fix wildcards *)
     val thm3 = CONV_RULE (RHS_CONV (RATOR_CONV (PMATCH_ROW_INTRO_WILDCARDS_CONV))) thm2
  in
     thm3
  end

  fun process_row (row, thm) = let
    val row_thm = process_row_aux row
    val thmA = PMATCH_EXTEND_BOTH
    val thmB = HO_MATCH_MP thmA row_thm
    val thmC = HO_MATCH_MP thmB thm
  in
    thmC
  end

  val base_thm = INST_TYPE [gamma |-> type_of t] (ISPECL [v, nv] PMATCH_EXTEND_BASE)
  val thm0 = List.foldl process_row base_thm (List.rev rows)
in
  thm0
end handle HOL_ERR _ => raise UNCHANGED


fun PMATCH_EXTEND_INPUT_CONV_GEN ssl = PMATCH_EXTEND_INPUT_CONV_GENCALL (ssl, NONE)
val PMATCH_EXTEND_INPUT_CONV = PMATCH_EXTEND_INPUT_CONV_GEN [];


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
    val (pt', _, _) = dest_PMATCH_ROW r
    val (_, pt) = pairSyntax.dest_pabs pt'
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
    val gen_fun = mk_var_gen (var_basename ^ "_") avoid;
    val new_vars =  map gen_fun types
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
     SOME thm
  end handle HOL_ERR _ => NONE

  val rows = List.rev rows
  val row_thms = map PMATCH_ROW_EXPAND_COLS rows
  val _ = if (exists isSome row_thms) then () else raise UNCHANGED

  fun process_row ((row_thm_opt, row), thm) = let
    val row_thm = case row_thm_opt of
        NONE => REFL (mk_comb (row, v))
      | SOME thm => thm
    val thmA = PMATCH_EXTEND_BOTH
    val thmB = HO_MATCH_MP thmA row_thm
    val thmC = HO_MATCH_MP thmB thm
  in
    thmC
  end

  val base_thm = INST_TYPE [gamma |-> type_of t] (ISPECL [v, v] PMATCH_EXTEND_BASE)
  val thm0 = foldl process_row base_thm (zip row_thms rows)
in
  thm0
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

val PMATCH_NORMALISE_CONV_AUX =
EVERY_CONV [
  TRY_CONV (QCHANGED_CONV PMATCH_CLEANUP_PVARS_CONV),
  TRY_CONV (QCHANGED_CONV PMATCH_FORCE_SAME_VARS_CONV),
  TRY_CONV (QCHANGED_CONV PMATCH_EXPAND_COLS_CONV),
  TRY_CONV (QCHANGED_CONV PMATCH_INTRO_WILDCARDS_CONV)
];

fun PMATCH_NORMALISE_CONV t =
  if (is_PMATCH t) then PMATCH_NORMALISE_CONV_AUX t else raise UNCHANGED;

val PMATCH_NORMALISE_ss =
    simpLib.conv_ss
      {name  = "PMATCH_NORMALISE_CONV",
       trace = 2,
       key   = SOME ([],``PMATCH (p:'a) (rows : ('a -> 'b option) list)``),
       conv  = K (K PMATCH_NORMALISE_CONV)}


fun PMATCH_SIMP_CONV_GENCALL_AUX rc_arg =
(TRY_CONV PMATCH_NORMALISE_CONV_AUX) THENC
REPEATC (FIRST_CONV [
  QCHANGED_CONV (PMATCH_CLEANUP_CONV_GENCALL rc_arg),
  QCHANGED_CONV (PMATCH_SIMP_COLS_CONV_GENCALL rc_arg),
  QCHANGED_CONV (PMATCH_REMOVE_FAST_REDUNDANT_CONV_GENCALL rc_arg),
  QCHANGED_CONV (PMATCH_REMOVE_FAST_SUBSUMED_CONV_GENCALL false rc_arg)
]);

fun PMATCH_SIMP_CONV_GENCALL rc_arg t =
  if (is_PMATCH t) then PMATCH_SIMP_CONV_GENCALL_AUX rc_arg t else
  raise UNCHANGED

fun PMATCH_SIMP_CONV_GEN ssl = PMATCH_SIMP_CONV_GENCALL (ssl, NONE)

val PMATCH_SIMP_CONV = PMATCH_SIMP_CONV_GEN [];

fun PMATCH_SIMP_GEN_ss ssl =
  make_gen_conv_ss PMATCH_SIMP_CONV_GENCALL "PMATCH_SIMP_REDUCER" ssl

val PMATCH_SIMP_ss = name_ss "patternMatchesSimp" (PMATCH_SIMP_GEN_ss [])
val _ = BasicProvers.augment_srw_ss [PMATCH_SIMP_ss];


fun PMATCH_FAST_SIMP_CONV_GENCALL_AUX rc_arg =
REPEATC (FIRST_CONV [
  QCHANGED_CONV (PMATCH_CLEANUP_CONV_GENCALL rc_arg),
  QCHANGED_CONV (PMATCH_SIMP_COLS_CONV_GENCALL rc_arg)
]);

fun PMATCH_FAST_SIMP_CONV_GENCALL rc_arg t =
  if (is_PMATCH t) then PMATCH_FAST_SIMP_CONV_GENCALL_AUX rc_arg t else
  raise UNCHANGED

fun PMATCH_FAST_SIMP_CONV_GEN ssl = PMATCH_FAST_SIMP_CONV_GENCALL (ssl, NONE)

val PMATCH_FAST_SIMP_CONV = PMATCH_FAST_SIMP_CONV_GEN [];

fun PMATCH_FAST_SIMP_GEN_ss ssl =
  make_gen_conv_ss PMATCH_FAST_SIMP_CONV_GENCALL "PMATCH_FAST_SIMP_REDUCER" ssl

val PMATCH_FAST_SIMP_ss = name_ss "patternMatchesFastSimp" (PMATCH_FAST_SIMP_GEN_ss [])


(***********************************************)
(* Remove double var bindings                  *)
(***********************************************)

fun force_unique_vars s no_change avoid t =
  case Psyntax.dest_term t of
      Psyntax.VAR (_, _) =>
      if tmem t no_change then (s, avoid, t) else
      let
         val v' = variant avoid t
         val avoid' = v'::avoid
         val s' = if v' ~~ t then s else ((v', t)::s)
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

  val (new_binds, _, p_tb') = force_unique_vars [] [] (free_vars p_t) p_tb
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

  val thm3 = CONV_RULE (RHS_CONV (DEPTH_CONV pairLib.GEN_BETA_CONV)) thm2

   val thm4 = CONV_RULE (RHS_CONV (RATOR_CONV (RAND_CONV (REWRITE_CONV [])))) thm3
in
  thm4
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
val t = ``case (x, y) of
  | (x, 2) when EVEN x => x + x
  | (SUC x, y) when ODD x => y + x + SUC x
  | (SUC x, 1) => x
  | (x, _) => x+3``

val rc_arg = ([], NONE)
val rows = 0
*)

fun PMATCH_REMOVE_GUARD_AUX rc_arg t = let
  val (v, rows) = dest_PMATCH t

  fun find_row_to_split rs1 rs = case rs of
     [] => raise UNCHANGED (* nothing found *)
   | (r:: rs') => let
        val (_, _, g, _) = dest_PMATCH_ROW_ABS r
        val g_simple = Teq g orelse Feq g
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
fun colRank_first_row (_:term, rows) =
  case rows of
    [] => 0
  | (vs, p) :: _ => if is_var p andalso tmem p vs then 0 else 1

fun colRank_first_row_constr db (_, rows) = case rows of
    [] => 0
  | ((vs, p) :: _) => if is_var p andalso tmem p vs then 0 else
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
        | aux n ((vs, p) :: pL) = if (is_var p)
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
     val cL_rows'' = Lib.op_mk_set aconv cL_rows'
  in
    SOME (cL_rows'', cL_cf, exh)
  end

fun tmltm_eq (tml1,tm1) (tml2,tm2) = tml_eq tml1 tml2 andalso tm1 ~~ tm2
fun col_get_nonvar_set (_, rows) =
  let
     val cL' = List.filter (fn (vs, p) => not (is_var p andalso tmem p vs)) rows
     val cL'' = Lib.op_mk_set tmltm_eq cL'
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
       ~(List.foldl (fn (c, s) => s + length (fst (strip_fun (type_of c)))) 0 cL)
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
val t = ``case (a,x,xs) of
    | (NONE,x,[]) when x > 5 => x
    | (NONE,x,_) => SUC x``

val t = ``case (a,x,xs) of
    | (NONE,x,[]) => x
    | (NONE,x,[2]) => x
    | (NONE,x,[v18]) => 3
    | (NONE,x,v12::v16::v17) => 3
    | (y,x,z,zs) .| (SOME y,x,[z]) => (x + 5 + z)
    | (y,v23,v24) .| (SOME y,0,v23::v24) => (v23 + y)
    | (y,z,v23) .| (SOME y,SUC z,[v23]) when (y > 5) => 3
    | (y,z) .| (SOME y,SUC z,[1; 2]) => (y + z)
  ``
*)

fun literal_case_CONV c tt = if boolSyntax.is_literal_case tt then
   RATOR_CONV (RAND_CONV (ABS_CONV c)) tt else c tt

val literal_cong_stop = prove(
   ``(v = v') ==> (literal_case (f:'a -> 'b) v = literal_case f v')``,
   SIMP_TAC std_ss [])

fun PMATCH_CASE_SPLIT_AUX rc_arg col_no expand_thm t = let
  val (v, rows) = dest_PMATCH t
  val vs = pairSyntax.strip_pair v

  val arg = el (col_no+1) vs
  val arg_v = genvar (type_of arg)
  val vs' = pairSyntax.list_mk_pair (fst (
    replace_element vs col_no [arg_v]))

  val ff = let
    val (x, xs) = strip_comb t
    val t' = list_mk_comb(x, vs' :: (tl xs))
  in
    mk_abs (arg_v, t')
  end

  val thm0 = ISPEC arg (ISPEC ff expand_thm)
  val thm1 = CONV_RULE (LHS_CONV BETA_CONV) thm0

  val c' = REPEATC (
    TRY_CONV (QCHANGED_CONV (PMATCH_CLEANUP_CONV_GENCALL rc_arg)) THENC
    TRY_CONV (QCHANGED_CONV (PMATCH_SIMP_COLS_CONV_GENCALL rc_arg)) THENC
    TRY_CONV (REWR_CONV PMATCH_INCOMPLETE_def)
  );

  fun c tt = let
    val _ = let
      val (t0, _) = dest_comb tt
      val (v', _) = dest_abs t0
    in
      if (aconv arg_v v') then () else failwith "not a new position"!
    end
  in
    (BETA_CONV THENC c') tt
  end;

  val thm2 = CONV_RULE (RHS_CONV (TOP_SWEEP_CONV c)) thm1

  (* check whether it got simpler, if not try full simp including propagating
     case information *)
  val thm3 = if (does_conv_loop thm2) then let
       val thm3 = CONV_RULE (RHS_CONV (literal_case_CONV (SIMP_CONV (
           (std_ss++simpLib.merge_ss (fst rc_arg) ++ PMATCH_SIMP_GEN_ss (fst rc_arg))) [PMATCH_INCOMPLETE_def, Cong literal_cong_stop]))) thm2
       val _ = if  (does_conv_loop thm3) then raise UNCHANGED else ()
       in thm3 end
     else thm2
in
  thm3
end

(*
val t = t'
val col_no = 1
val rc_arg = ([], NONE)
val gl = []
val callback_opt = NONE
val db = !thePmatchCompileDB
val col_heu = colHeu_default
val t = ``case x of 3 => 1 | _ => 0``
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
             val (cols', _) = replace_element cols col_no []
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
  val rows_tm = rand t'

  fun mk_pair avoid acc col_no v = if (col_no <= 1) then (
      let
        val vs = List.rev (v::acc)
        val p = pairSyntax.list_mk_pair vs
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
  case (a,x,xs) of
    | (NONE,_,[]) => 0
    | (NONE,x,[]) when x < 10 => x
    | (NONE,x,[2]) => x
    | (NONE,x,[v18]) => 3
    | (NONE,_,[_;_]) => x
    | (NONE,x,v12::v16::v17) => 3
    | (SOME y,x,[z]) => x + 5 + z
    | (SOME y,0,v23::v24) => (v23 + y)
    | (SOME y,SUC z,[v23]) when y > 5 => 3
    | (SOME y,SUC z,[1; 2]) => y + z``;

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
        val (cols', _) = replace_element cols col_no []
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
    val thm03 =
        RIGHT_CONV_RULE (DESCEND_CONV BINOP_CONV (TRY_CONV EXISTS_OR_CONV))
                        thm02

    val thm04 = RIGHT_CONV_RULE (ALL_DISJ_CONV exists_left_and_label_CONV) thm03

    val LEFT_RIGHT_AND_LIST_EXISTS_CONV =
        DESCEND_CONV QUANT_CONV
                     (RIGHT_AND_EXISTS_CONV ORELSEC LEFT_AND_EXISTS_CONV)
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

    fun compile (thm, cols, lbl) = let
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
  case (x,y,z) of
    | (NONE,_,[]) => 0
    | (NONE,x,[]) when x < 10 => x
    | (NONE,x,[2]) => x
    | (NONE,x,[v18]) => 3
    | (NONE,_,[_;_]) => 4
    | (NONE,x,v12::v16::v17) => 3
    | (SOME y,x,[z]) => x + 5 + z
    | (SOME y,0,v23::v24) => (v23 + y)
    | (SOME y,SUC z,[v23]) when y > 5 => 3
    | (SOME y,SUC z,[1; 2]) => y + z
  ``;

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
    | (t::ts) =>
      if tmem t vs then aux ts
      else if pairSyntax.is_pair t then
          aux ((pairSyntax.strip_pair t)@ts)
      else (
          case pmatch_compile_db_dest_constr_term db t of
             NONE => SOME t
           | SOME (_, args) => aux ((map snd args) @ ts)
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
val t = ``case (x, z) of
  | (NONE, NONE) => 0
  | (SOME _, _) => 1
  | (_, SOME _) => 2
``

val t = ``case (x, z) of
  | (NONE, NONE) => 0
  | (SOME _, _) => 1
  | (_, NONE) => 2
``

val t = ``case (x, z) of
  | (NONE, 1) => 0
  | (SOME _, 2) => 1
  | (_, x) when x > 5 => 2
``
*)

fun IS_REDUNDANT_ROWS_INFO_WEAKEN_RULE info_thm = let
  val (conds, _) = listSyntax.dest_list (rand (concl info_thm))
  val conds' = List.map (fn c => if (aconv c T) then T else F) conds
  val _ = if exists (aconv T) conds' then () else raise UNCHANGED
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
  proofManagerLib.set_goal ([], t)
end;


(*************************************)
(* Exhaustiveness                    *)
(*************************************)

fun PMATCH_IS_EXHAUSTIVE_FAST_CHECK_GENCALL rc_arg t = let
  val (v, rows) = dest_PMATCH t

  fun check_row r = let
    val r_tm = mk_eq (mk_comb (r, v), optionSyntax.mk_none (type_of t))
    val r_thm = rc_conv rc_arg r_tm
    val res_tm = rhs (concl r_thm)
  in
    if (same_const res_tm T) then SOME (true, r_thm) else
    (if (same_const res_tm F) then SOME (false, r_thm) else NONE)
  end handle HOL_ERR _ => NONE

  fun find_thms a thmL [] = (a, thmL)
    | find_thms a thmL (r::rows) = (
      case (check_row r) of
         NONE => find_thms true thmL rows
       | SOME (true, r_thm) => find_thms a (r_thm :: thmL) rows
       | SOME (false, r_thm) => (false, [r_thm]))

  val (abort, rewrite_thms) = find_thms false [] (List.rev rows)
  val _ = if abort then raise UNCHANGED else ()

  val t0 = mk_PMATCH_IS_EXHAUSTIVE v (rand t)
in
  REWRITE_CONV (PMATCH_IS_EXHAUSTIVE_REWRITES::rewrite_thms) t0
end;

fun PMATCH_IS_EXHAUSTIVE_FAST_CHECK_GEN ssl =
    PMATCH_IS_EXHAUSTIVE_FAST_CHECK_GENCALL (ssl, NONE)

val PMATCH_IS_EXHAUSTIVE_FAST_CHECK =
    PMATCH_IS_EXHAUSTIVE_FAST_CHECK_GEN [];

(*
val db = !thePmatchCompileDB
val col_heu = colHeu_default
val rc_arg = ([], NONE)
*)


(*
val t = ``case (x, z) of
  | (NONE, NONE) => 0
  | (_, SOME _) => 2
``

val t = ``case (x, z) of
  | (NONE, NONE) => 0
  | (SOME _, _) => 1
  | (_, NONE) => 2
``

val t = ``case (x, z) of
  | (NONE, 1) => 0
  | (SOME _, 2) => 1
  | (_, x) when x > 5 => 2
``

val info_thm = COMPUTE_REDUNDANT_ROWS_INFO_OF_PMATCH t

*)


fun IS_REDUNDANT_ROWS_INFO_TO_PMATCH_IS_EXHAUSTIVE info_thm = let
  val thm0 = MATCH_MP IS_REDUNDANT_ROWS_INFO_EXTRACT_IS_EXHAUSTIVE
    info_thm
in
  thm0
end

fun PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK_FULLGEN db col_heu rc_arg t = let
  val info_thm = COMPUTE_REDUNDANT_ROWS_INFO_OF_PMATCH_GENCALL rc_arg db col_heu t
in
  IS_REDUNDANT_ROWS_INFO_TO_PMATCH_IS_EXHAUSTIVE info_thm
end

fun PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK_GENCALL rc_arg t =
  PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK_FULLGEN
    (!thePmatchCompileDB) colHeu_default rc_arg t

fun PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK_GEN ssl =
  PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK_GENCALL (ssl, NONE)

val PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK =
  PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK_GEN [];


val IMP_TO_EQ_THM = prove (``!P Q. (P ==> Q) ==> (~P ==> ~Q) ==> (Q <=> P)``, PROVE_TAC[])

fun PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK_FULLGEN db col_heu rc_arg t = let
  val thm0 = PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK_FULLGEN db col_heu rc_arg t
in
  let
    val thm = rc_elim_precond rc_arg thm0
  in
    EQT_INTRO thm
  end handle HOL_ERR _ => let
    val thm1 = MATCH_MP IMP_TO_EQ_THM thm0

    val (precond, _) = dest_imp_only (concl thm1)
    val pre_thm = prove_attempt (precond,
      REWRITE_TAC[PMATCH_IS_EXHAUSTIVE_REWRITES, PMATCH_ROW_EQ_NONE, PMATCH_ROW_COND_EX_def,
        DISJ_IMP_THM, GSYM LEFT_FORALL_IMP_THM] THEN
      SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [PMATCH_ROW_COND_DEF_GSYM] THEN
      rc_tac rc_arg)

    val thm2 = MP thm1 pre_thm
  in
    thm2
  end
end

fun PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK_GENCALL rc_arg t =
  PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK_FULLGEN
    (!thePmatchCompileDB) colHeu_default rc_arg t

fun PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK_GEN ssl =
  PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK_GENCALL (ssl, NONE)

val PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK =
  PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK_GEN [];


fun PMATCH_IS_EXHAUSTIVE_CHECK_FULLGEN db col_heu rc_arg t =
  QCHANGED_CONV (PMATCH_IS_EXHAUSTIVE_FAST_CHECK_GENCALL rc_arg) t
  handle HOL_ERR _ =>
    PMATCH_IS_EXHAUSTIVE_COMPILE_CHECK_FULLGEN db col_heu rc_arg t;

fun PMATCH_IS_EXHAUSTIVE_CHECK_GENCALL rc_arg t =
  PMATCH_IS_EXHAUSTIVE_CHECK_FULLGEN (!thePmatchCompileDB) colHeu_default rc_arg t

fun PMATCH_IS_EXHAUSTIVE_CHECK_GEN ssl =
  PMATCH_IS_EXHAUSTIVE_CHECK_GENCALL (ssl, NONE)

val PMATCH_IS_EXHAUSTIVE_CHECK = PMATCH_IS_EXHAUSTIVE_CHECK_GEN []


local
  val EQ_F_ELIM = prove (``!b. F ==> b``, PROVE_TAC[])
  val EQ_T_ELIM = prove (``!b. (b = T) ==> ~F ==> b``, PROVE_TAC[])
  val EQ_O_ELIM = prove (``!b1 b2. (b1 = b2) ==> b2 ==> b1``, PROVE_TAC[])

in

fun PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK_FULLGEN db col_heu rc_arg t = let
    val thm0 = QCHANGED_CONV (PMATCH_IS_EXHAUSTIVE_FAST_CHECK_GENCALL rc_arg) t
    val (ex_t, r) = dest_eq (concl thm0)
  in
    if Teq r then
      MP (SPEC ex_t EQ_T_ELIM) thm0
    else if Feq r then
      SPEC ex_t EQ_F_ELIM
    else
      MP (SPEC r (SPEC ex_t EQ_O_ELIM)) thm0
  end handle HOL_ERR _ =>
    PMATCH_IS_EXHAUSTIVE_COMPILE_CONSEQ_CHECK_FULLGEN db col_heu rc_arg t
end;


fun PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK_GENCALL rc_arg t =
  PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK_FULLGEN (!thePmatchCompileDB) colHeu_default rc_arg t

fun PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK_GEN ssl =
  PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK_GENCALL (ssl, NONE)

val PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK = PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK_GEN []


(*************************************)
(* Nchotomy                          *)
(*************************************)

(*
val db = !thePmatchCompileDB
val col_heu = colHeu_default
val rc_arg = ([], NONE)
*)


val neg_imp_rewr = prove (``(~A ==> B) = (~B ==> A)``, tautLib.PTAUT_TAC);

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
val t = ``case (x, y) of ([], x::xs) => x | (_, _) => 2``
val t = ``case (x, y) of ([], x::xs) => x``
*)

fun PMATCH_COMPLETE_CONV_GENCALL_AUX rc_arg db col_heu use_guards t =
let
  val exh_thm = EQT_ELIM (PMATCH_IS_EXHAUSTIVE_FAST_CHECK_GENCALL rc_arg t)
                handle UNCHANGED => failwith "NOT EXH"
in (false, REFL t, (fn () => exh_thm)) end handle HOL_ERR _ =>
let
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
  end handle HOL_ERR _ => []

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

  val thm_expand = foldl add_missing_pat (REFL t) missing_list

  (* set_goal ([], mk_PMATCH_IS_EXHAUSTIVE v (rand (rhs (concl thm_expand)))) *)
  fun exh_thm () = prove (mk_PMATCH_IS_EXHAUSTIVE v (rand (rhs (concl thm_expand))),
    ASSUME_TAC (thm_nchot) THEN
    PURE_REWRITE_TAC [PMATCH_IS_EXHAUSTIVE_REWRITES, PMATCH_ROW_NEQ_NONE] THEN
    PROVE_TAC[])
in
  (not (List.null missing_list), thm_expand, exh_thm)
end

fun PMATCH_COMPLETE_CONV_GENCALL rc_arg db col_heu use_guards t =
  let
    val (ch, thm, _) = (PMATCH_COMPLETE_CONV_GENCALL_AUX rc_arg db col_heu use_guards t)
    val _ = if ch then () else raise UNCHANGED
  in thm end;

fun PMATCH_COMPLETE_CONV_GEN ssl =
    PMATCH_COMPLETE_CONV_GENCALL (ssl, NONE);

fun PMATCH_COMPLETE_CONV use_guards =
    PMATCH_COMPLETE_CONV_GEN [] (!thePmatchCompileDB) colHeu_default use_guards;

fun PMATCH_COMPLETE_GEN_ss ssl db colHeu use_guards =
  make_gen_conv_ss (fn rc_arg =>
    PMATCH_COMPLETE_CONV_GENCALL rc_arg db colHeu use_guards)
    "PMATCH_COMPLETE_REDUCER" ssl;

fun PMATCH_COMPLETE_ss use_guards = PMATCH_COMPLETE_GEN_ss [] (!thePmatchCompileDB) colHeu_default use_guards;


fun PMATCH_COMPLETE_CONV_GEN_WITH_EXH_PROOF ssl db col_heu use_guards t =
    let val (ch, mt, rt) = PMATCH_COMPLETE_CONV_GENCALL_AUX (ssl, NONE) db col_heu use_guards t in
    (if ch then SOME mt else NONE, rt ()) end

fun PMATCH_COMPLETE_CONV_WITH_EXH_PROOF use_guards =
    PMATCH_COMPLETE_CONV_GEN_WITH_EXH_PROOF [] (!thePmatchCompileDB) colHeu_default use_guards;



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

val tm = ``(P2 /\ Q ==> (
  (case xx of
    | (x, y::ys) => (x + y)
    | (0, []) => 9
    | (x, []) when x > 3 => x
    | (x, []) => 0) = 5))``

val tm = ``
  (case xx of
    | (x, y::ys) => (x + y)
    | (0, []) => 9
    | (x, []) when x > 3 => x
    | (x, []) => 0) = 5``

val _ = ENABLE_PMATCH_CASES()
val OPT_PAIR_def = TotalDefn.Define `OPT_PAIR xy = case xy of
 | (NONE, _) => NONE
 | (_, NONE) => NONE
 | (SOME x, SOME y) => SOME (x, y)`
val thm = OPT_PAIR_def
val tm = concl (hd (BODY_CONJUNCTS thm))
val force_minimal = false
val rc_arg = ([], NONE)
val try_exh = true
*)


local
val IMP_AUX_THM = prove (``(P ==> (X <=> Y)) <=>
   ((P ==> X) <=> (P ==> Y))``, PROVE_TAC[])
in
fun SIMPLE_IMP_COND_REWRITE_CONV thm tt = let
  val (pre, post) = dest_imp tt
  val pre_thm = ASSUME pre
  val rewr_thm = MATCH_MP thm pre_thm
  val thm0 = REWRITE_CONV [rewr_thm] post
  val thm1 = DISCH pre thm0
  val thm2 = CONV_RULE (REWR_CONV IMP_AUX_THM) thm1
in
  thm2
end
end;

fun rename_uscore_vars ren avoid [] = ren
  | rename_uscore_vars ren avoid (v::vs) =
    let
      val (v_n, v_ty) = dest_var v
      val _ = if (String.sub(v_n, 0) = #"_") then () else failwith "nothing to do"
      val v' = variant avoid (mk_var ("v", v_ty))
    in
      rename_uscore_vars ((v |-> v')::ren) (v'::avoid) vs
    end handle HOL_ERR _ => rename_uscore_vars ren avoid vs



fun PMATCH_LIFT_BOOL_CONV_GENCALL force_minimal try_exh rc_arg tm = let
  (* check whether we should really process tm *)
  val _ = if type_of tm = bool then () else raise UNCHANGED
  val p_tm = find_term is_PMATCH tm
  fun has_subterm p t = (find_term p t; true) handle HOL_ERR _ => false

  val is_minimal = not force_minimal orelse not (has_subterm (fn t =>
    (not (aconv t tm)) andalso
    (type_of t = bool) andalso
    (has_subterm is_PMATCH t)) tm)
  val _ = if is_minimal then () else raise UNCHANGED

  (* prepare tm *)
  val v = genvar (type_of p_tm)
  val P_tm = mk_abs (v, subst [p_tm |-> v] tm)
  val P_v = genvar (type_of P_tm)

  (* do real work *)
  val thm0 = let
    val (p_tm', genvars_elim_s) = PMATCH_INTRO_GENVARS p_tm
    val t0 = (mk_comb (P_v, p_tm'))
    val c1 = SIMP_CONV std_ss [PMATCH_EXPAND_PRED_THM,
      PMATCH_EXPAND_PRED_def, PMATCH_ROW_NEQ_NONE,
      EVERY_DEF, PMATCH_ROW_EVAL_COND_EX, REVERSE_REV, REV_DEF]
    val c2 = REWRITE_CONV [PMATCH_ROW_COND_EX_def,
      PULL_EXISTS]

    val thm00 = (c1 THENC c2) t0
    val thm01 = INST genvars_elim_s thm00
  in
    thm01
  end

  (* Elim choice *)
  val thm1 = let
    val (v, rows) = dest_PMATCH p_tm
    fun process_row (r, thm') = let
      val (pt, gt, rt) = dest_PMATCH_ROW r
      val thm00 = ISPECL [pt, gt, v] (FRESH_TY_VARS_RULE PMATCH_COND_SELECT_UNIQUE)
      val thm01 = rc_elim_precond rc_arg thm00
      val thm'' = CONV_RULE (DEPTH_CONV (SIMPLE_IMP_COND_REWRITE_CONV thm01)) thm'
    in
      thm''
    end handle HOL_ERR _ => thm'
  in
    foldl process_row thm0 rows
  end

  (* get rid of exhaustiveness check *)
  val thm2 = let
    val _ = if try_exh then () else failwith "skip"
    val thm_ex = PMATCH_IS_EXHAUSTIVE_CHECK_GENCALL rc_arg p_tm
    val thm2 = CONV_RULE (RHS_CONV (REWRITE_CONV [thm_ex])) thm1
  in
    thm2
  end handle HOL_ERR _ => thm1
           | UNCHANGED => thm1


  (* Use the right variable names and simplify *)
  val thm3 = let
    fun special_CONV tt = let
      val (vars_tm0, row) = let
        val (_, tt0) = dest_forall tt
        val (tt1, _) = dest_imp_only tt0
        val (tt2, _, _, _) = dest_PMATCH_ROW_COND tt1
      in (fst (pairSyntax.dest_pabs tt2), tt1) end

      val vars_tm = let
        val to_ren = free_vars vars_tm0
        val avoid = free_vars row @ to_ren
        val ren = rename_uscore_vars [] avoid to_ren
      in
        subst ren vars_tm0
      end

     val intro_marker = TRY_CONV (QUANT_CONV (RAND_CONV (RATOR_CONV (RAND_CONV markerLib.stmark_term))))

      val elim_COND_CONV =
        QUANT_CONV (RATOR_CONV (RAND_CONV (REWR_CONV PMATCH_ROW_COND_DEF_GSYM)))

      val intro_CONV = RAND_CONV (pairTools.PABS_INTRO_CONV vars_tm)
      val elim_CONV = TRY_CONV (pairTools.ELIM_TUPLED_QUANT_CONV)
      val eval_preconds = STRIP_QUANT_CONV (RAND_CONV (fn t => let
         val _ = dest_imp_only t
       in RATOR_CONV (RAND_CONV (rc_conv rc_arg)) t end))

      val simp_CONV = TRY_CONV (SIMP_CONV std_ss [])

      val elim_marker =
        (REWR_CONV markerTheory.stmarker_def) THENC
        TRY_CONV (rc_conv rc_arg)
    in
      EVERY_CONV [
        intro_marker,
        elim_COND_CONV,
        intro_CONV, elim_CONV,
        simp_CONV,
        DEPTH_CONV elim_marker,
        TRY_CONV (REWRITE_CONV [])
        ] tt
    end
  in
    CONV_RULE (RHS_CONV (ALL_CONJ_CONV special_CONV)) thm2
  end


  (* restore original predicate *)
  val thm4 = let
    val thm00 = INST [P_v |-> P_tm] thm3
    val thm01 = CONV_RULE (LHS_CONV BETA_CONV) thm00
    val thm02 = CONV_RULE (RHS_CONV (DEPTH_CONV BETA_CONV)) thm01
    val _ = assert (fn thm => aconv (lhs (concl thm)) tm) thm02
  in
    thm02
  end
in
  thm4
end

fun PMATCH_LIFT_BOOL_CONV_GEN ssl try_exh = PMATCH_LIFT_BOOL_CONV_GENCALL true try_exh (ssl, NONE)

val PMATCH_LIFT_BOOL_CONV = PMATCH_LIFT_BOOL_CONV_GEN [];

fun PMATCH_LIFT_BOOL_GEN_ss ssl try_exh =
  make_gen_conv_ss (PMATCH_LIFT_BOOL_CONV_GENCALL true try_exh) "PMATCH_LIFT_BOOL_REDUCER" ssl

val PMATCH_LIFT_BOOL_ss = PMATCH_LIFT_BOOL_GEN_ss []


fun PMATCH_TO_TOP_RULE_SINGLE ssl thm = let
  val thm0 = GEN_ALL thm

  val thm1 = CONV_RULE (STRIP_QUANT_CONV (PMATCH_LIFT_BOOL_CONV_GENCALL false false (ssl, NONE))) thm0
  val thm2 = CONV_RULE (STRIP_QUANT_CONV (
     EVERY_CONJ_CONV (STRIP_QUANT_CONV (TRY_CONV (RAND_CONV markerLib.stmark_term))))) thm1
  val thm3 = SIMP_RULE std_ss [FORALL_AND_THM,
   Cong (REFL ``stmarker (t:'a)``)] thm2
  val thm4 = PURE_REWRITE_RULE [markerTheory.stmarker_def] thm3

  val thm5 = LIST_CONJ (butlast (CONJUNCTS thm4))
in
  thm5
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


(*************************************)
(* Lifting                           *)
(*************************************)

(*
val tm = ``\y. SUC (SUC
  (case y of
    | (x, y::ys) => (x + y)
    | (0, []) => 0)) +
  (case xx of
    | (x, y::ys) => (x + y)
    | (0, []) => 0)``
val tm = p_tm
*)

fun PMATCH_LIFT_CONV_GENCALL_AUX rc_arg db col_heu tm = let
  (* check whether we should really process tm *)
  val _ = if (is_PMATCH tm) then failwith "PMATCH_LIFT_CONV_GENCALL_AUX: nothing to do" else ()

  (* search subterm to lift *)
  fun search_pred (bvs, tt) = if is_PMATCH tt andalso
    HOLset.isEmpty (HOLset.intersection (HOLset.fromList Term.compare bvs, FVL [tt] empty_tmset)) then SOME tt else NONE
  val p_tm = case gen_find_term search_pred tm of SOME p_tm => p_tm | NONE => failwith "no_case"

  (* Abstract context with f_tm *)
  val f_tm = let
    val nv = genvar (type_of p_tm)
    val tm' = subst [p_tm |-> nv] tm
  in
    mk_abs (nv, tm')
  end
  val (_, p_thm, exh_thm) = PMATCH_COMPLETE_CONV_GENCALL_AUX rc_arg db col_heu true p_tm

  (* Intro f_tm *)
  val thm0 = let
    val f_tm_thm = GSYM (BETA_CONV (mk_comb (f_tm, p_tm)))
    val f_tm_thm' = CONV_RULE (RHS_CONV (RAND_CONV (K p_thm))) f_tm_thm
  in f_tm_thm' end

  (* Apply lifting thm *)
  val (v, rows_tm, thm1) = let
    val p_tm' = rhs (concl p_thm)
    val (v, rows) = dest_PMATCH p_tm'
    val rows_tm = rand p_tm'
    val thm10 = ISPECL [f_tm, v, rows_tm] (FRESH_TY_VARS_RULE PMATCH_LIFT_THM)
    val thm11 = MP thm10 (exh_thm())
  in (v, rows_tm, thm11) end

  (* Simplify *)
  val thm2 = let
    fun c3 tt = let
      val (vt, _) = pairSyntax.dest_pabs (rator (rand (snd (dest_abs tt))))
      val c30 = (pairTools.PABS_INTRO_CONV vt)
      val c31 = PairRules.PABS_CONV (RAND_CONV PairRules.PBETA_CONV)
      val c32 = PairRules.PABS_CONV BETA_CONV
    in
      (c30 THENC (TRY_CONV c31) THENC c32) tt
    end
    val c2 = REWR_CONV PMATCH_ROW_LIFT_THM THENC (RAND_CONV c3)
    val c = listLib.MAP_CONV c2
    val thm2 = c (rand (rhs (concl thm1)))
  in
    thm2
  end

  val thm_lift = CONV_RULE (RHS_CONV (RAND_CONV (K thm2))) (TRANS thm0 thm1)

  (* construct exhaustiveness result *)
  fun exh_thm' () = let
    val exh_thm = exh_thm ()
    val thm00 = ISPECL [f_tm, v, rows_tm] PMATCH_IS_EXHAUSTIVE_LIFT
    val thm01 = MP thm00 exh_thm
    val thm02 = CONV_RULE (RAND_CONV (K thm2)) thm01
  in thm02 end
in
  (thm_lift, exh_thm')
end;


fun PMATCH_LIFT_CONV_GENCALL rc_arg db col_heu t =
  let
    val (thm, _) = (PMATCH_LIFT_CONV_GENCALL_AUX rc_arg db col_heu t)
  in thm end;

fun PMATCH_LIFT_CONV_GENCALL_WITH_EXH_PROOF rc_arg db col_heu t =
  let
    val (thm, exh) = (PMATCH_LIFT_CONV_GENCALL_AUX rc_arg db col_heu t)
  in (thm, exh()) end;

fun PMATCH_LIFT_CONV_GEN ssl =
    PMATCH_LIFT_CONV_GENCALL (ssl, NONE);

fun PMATCH_LIFT_CONV t =
    PMATCH_LIFT_CONV_GEN [] (!thePmatchCompileDB) colHeu_default t;

fun PMATCH_LIFT_CONV_GEN_WITH_EXH_PROOF ssl =
    PMATCH_LIFT_CONV_GENCALL_WITH_EXH_PROOF (ssl, NONE);

fun PMATCH_LIFT_CONV_WITH_EXH_PROOF t =
    PMATCH_LIFT_CONV_GEN_WITH_EXH_PROOF [] (!thePmatchCompileDB) colHeu_default t;


(*************************************)
(* FLATTENING                        *)
(*************************************)

(*
val do_lift = false
val use_guards = true
val rc_arg = ([], NONE)
val db = !thePmatchCompileDB
val col_heu = colHeu_default


val tm = ``case (x, y) of ([], x::xs) => (
           case xs of [] => 0 | _ => 5) | (_, []) => 1 ``

val tm = ``case (x, y) of (x::xs, []) => 2 | ([], x::xs) => (
           SUC (case xs of [] => x | _ => HD xs)) | (_, []) => 1 ``
*)

fun PMATCH_FLATTEN_CONV_GENCALL_AUX rc_arg db col_heu do_lift tm = let
  val (v, rows) = dest_PMATCH tm

  (* Try to flatten row no i *)
  fun try_row i = let
    val (rows_b, row, rows_a) = extract_element rows i
    val (pt, gt, rt0) = dest_PMATCH_ROW row
    val (vs, rt) = pairSyntax.dest_pabs rt0

    (* lift the rhs of row i to be PMATCH expression *)
    val thm0 = if do_lift andalso not (is_PMATCH rt) then
      PMATCH_LIFT_CONV_GENCALL rc_arg db col_heu rt
    else
      PMATCH_COMPLETE_CONV_GENCALL rc_arg db col_heu true rt handle UNCHANGED => REFL rt

    (* extend the input to match the output of the outer PMATCH exactly *)
    val thm1 = let
      val thm1a = PMATCH_EXTEND_INPUT_CONV_GENCALL rc_arg vs (rhs (concl thm0))
      val thm1 = TRANS thm0 thm1a
    in thm1 end


    (* Apply the flatten theorem, discard preconditions and show that rhs equals input *)
    val thm2 = let
      val rt' = rhs (concl thm1)
      val (v', rows') = dest_PMATCH rt'
      val rows'' = map (fn t => pairSyntax.mk_pabs (v', t)) rows'


      (* instantiate thm *)
      val thm2a = let
        val thm20 = FRESH_TY_VARS_RULE PMATCH_FLATTEN_THM
        val thm20 = ISPEC v thm20
        val thm20 = ISPEC pt thm20
        val thm20 = ISPEC gt thm20
        val thm20 = ISPEC (listSyntax.mk_list(rows_b, type_of row)) thm20
        val thm20 = ISPEC (listSyntax.mk_list(rows_a, type_of row)) thm20
        val thm20 = ISPEC (listSyntax.mk_list(rows'', type_of (hd rows''))) thm20
        val thm21 = CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (pairTools.PABS_INTRO_CONV v')))) thm20
        val c = RATOR_CONV (RAND_CONV (RAND_CONV (pairTools.PABS_INTRO_CONV v')))
        val thm22 = CONV_RULE (RAND_CONV (LHS_CONV (RAND_CONV (RAND_CONV c)))) thm21

      in thm22 end

      (* simplify MAP (\x. r x) rows'' = rows' *)
      val thm2b = let
        val map_tm = rand (snd (pairSyntax.dest_pforall (fst (dest_imp (concl thm2a)))))
        val map_tm_eq = mk_eq (map_tm, listSyntax.mk_list (rows', type_of (hd rows')))
        val map_thm = prove (map_tm_eq, SIMP_TAC list_ss [])

        val thm2b = CONV_RULE (DEPTH_CONV (REWR_CONV map_thm)) thm2a
      in thm2b end

      (* elim precond *)
      val thm2c = let
        val exh_thm = PMATCH_IS_EXHAUSTIVE_CHECK_GENCALL rc_arg rt'
        val (pre, _) = dest_imp (concl thm2b)
        val pre_thm = prove (pre, SIMP_TAC std_ss [exh_thm, GSYM pairTheory.PFORALL_THM])
        val thm2c = MP thm2b pre_thm
      in thm2c end

      (* use thm1 on lhs *)
      val thm2d = let
        val c = RATOR_CONV (RAND_CONV (RAND_CONV (PairRules.PABS_CONV (K (GSYM thm1)))))
        val thm20 = CONV_RULE (LHS_CONV (RAND_CONV (RAND_CONV c))) thm2c
        val l_eq = mk_eq (tm, lhs (concl thm20))
        val l_thm = prove (l_eq, SIMP_TAC list_ss [])
        val thm2d = TRANS l_thm thm20
      in thm2d end
    in
      thm2d
    end

    (* EVALUATE MAP PMATCH_FLATTEN_FUN on rhs *)
    val thm3 = let
      val flatten_thm = let
        val thm00 = FRESH_TY_VARS_RULE PMATCH_FLATTEN_FUN_PMATCH_ROW
        val thm01 = ISPEC pt thm00
        val thm02 = rc_elim_precond rc_arg thm01
        val thm03 = ISPEC gt thm02
        val c = pairTools.PABS_INTRO_CONV vs
        val thm04 = CONV_RULE (STRIP_QUANT_CONV (LHS_CONV (RAND_CONV c))) thm03
      in thm04 end

      fun flatten_fun_conv tt = let
        val (_, row_d) = pairSyntax.dest_pabs (rand tt)
        val (pt_d, gt_d, rt_d) = dest_PMATCH_ROW row_d
        val thm00 = ISPECL [pt_d, pairSyntax.mk_pabs(vs, gt_d), pairSyntax.mk_pabs(vs, rt_d)] flatten_thm
        val eq_tm = mk_eq (tt, lhs (concl thm00))
        val eq_thm = prove (eq_tm, SIMP_TAC (std_ss++pairSimps.gen_beta_ss) [])

        val thm01 = TRANS eq_thm thm00
        val (vs', _) = pairSyntax.dest_pabs pt_d
        val thm02 = CONV_RULE (RHS_CONV (PMATCH_ROW_PABS_INTRO_CONV vs')) thm01

        val thm03 = CONV_RULE (RHS_CONV (DEPTH_CONV (pairLib.PAIRED_BETA_CONV ORELSEC BETA_CONV))) thm02
        val thm04 = CONV_RULE (RHS_CONV (REWRITE_CONV [])) thm03
      in thm04 end

      val c = BETA_CONV THENC flatten_fun_conv
      val thm30 = CONV_RULE (RHS_CONV (RAND_CONV (RATOR_CONV (
             RAND_CONV (RAND_CONV (listLib.MAP_CONV c)))))) thm2

      val thm31 = CONV_RULE (RHS_CONV (RAND_CONV (RATOR_CONV (RAND_CONV
        listLib.APPEND_CONV)))) thm30

      val thm32 = CONV_RULE (RHS_CONV (RAND_CONV
        listLib.APPEND_CONV)) thm31
    in thm32 end

    (* Fix wildcards *)
    val thm4 = CONV_RULE (RHS_CONV PMATCH_INTRO_WILDCARDS_CONV) thm3
  in
    thm4
  end

  val row_index_l = Lib.upto 0 (length rows - 1)
in
  tryfind try_row row_index_l
end


fun PMATCH_FLATTEN_CONV_GENCALL rc_arg db col_heu do_lift =
  REPEATC (PMATCH_FLATTEN_CONV_GENCALL_AUX rc_arg db col_heu do_lift)

fun PMATCH_FLATTEN_CONV_GEN ssl =
    PMATCH_FLATTEN_CONV_GENCALL (ssl, NONE);

fun PMATCH_FLATTEN_CONV do_lift =
    PMATCH_FLATTEN_CONV_GEN [] (!thePmatchCompileDB) colHeu_default do_lift;

fun PMATCH_FLATTEN_GEN_ss ssl db col_heu do_lift =
  make_gen_conv_ss (fn rc_arg => PMATCH_FLATTEN_CONV_GENCALL rc_arg db col_heu do_lift)
    "PMATCH_FLATTEN_REDUCER" ssl

fun PMATCH_FLATTEN_ss do_lift =
  PMATCH_FLATTEN_GEN_ss [] (!thePmatchCompileDB) colHeu_default do_lift;


(*************************************)
(* Analyse PMATCH expressions to     *)
(* check whether they can be         *)
(* translated to ML or OCAML         *)
(*************************************)

type pmatch_info = {
  pmi_is_well_formed            : bool,
  pmi_ill_formed_rows           : int list,
  pmi_has_free_pat_vars         : (int * term list) list,
  pmi_has_unused_pat_vars       : (int * term list) list,
  pmi_has_double_bound_pat_vars : (int * term list) list,
  pmi_has_guards                : int list,
  pmi_has_lambda_in_pat         : int list,
  pmi_has_non_contr_in_pat      : (int * term list) list,
  pmi_exhaustiveness_cond       : thm option
}

fun is_proven_exhaustive_pmatch (pmi : pmatch_info) =
  (case (#pmi_exhaustiveness_cond pmi) of
      NONE => false
    | SOME thm => let
        val (pre, _) = dest_imp_only (concl thm)
      in
        aconv pre ``~F``
      end handle HOL_ERR _ => false
  )

fun get_possibly_missing_patterns (pmi : pmatch_info) =
  (case (#pmi_exhaustiveness_cond pmi) of
      NONE => NONE
    | SOME thm => (let
        val (pre, _) = dest_imp_only (concl thm)
      in if aconv pre ``~F`` then SOME [] else
      let
        val ps = strip_disj (dest_neg pre)
        fun dest_p p = let
           val (_, vs, p, g) = dest_PMATCH_ROW_COND_EX_ABS p
        in (vs, p, g) end
      in
        SOME (List.map dest_p ps)
      end end) handle HOL_ERR _ => NONE
  )

fun extend_possibly_missing_patterns t (pmi : pmatch_info) =
  case get_possibly_missing_patterns pmi of
      NONE => failwith "no missing row info available"
    | SOME [] => t
    | SOME rs => let
       val use_guards = not (null (#pmi_has_guards pmi))
       val arb_t = mk_arb (type_of t)
       fun mk_row (v, p, g) = let
         val vars = pairSyntax.strip_pair v
       in
         snd (mk_PMATCH_ROW_PABS_WILDCARDS vars (p,
           if use_guards then g else T, arb_t))
       end
       val rows = List.map mk_row rs

       val (i, rows_org) = dest_PMATCH t
       val rows_t =
         listSyntax.mk_list (rows_org @ rows, type_of (hd rows))
      in
        mk_PMATCH i rows_t
      end;


fun is_well_formed_pmatch (pmi : pmatch_info) =
  (#pmi_is_well_formed pmi) andalso
  (null (#pmi_ill_formed_rows pmi)) andalso
  (null (#pmi_has_unused_pat_vars pmi)) andalso
  (null (#pmi_has_lambda_in_pat pmi));

fun is_ocaml_pmatch (pmi : pmatch_info) =
  (is_well_formed_pmatch pmi) andalso
  (null (#pmi_has_non_contr_in_pat pmi)) andalso
  (null (#pmi_has_free_pat_vars pmi)) andalso
  (null (#pmi_has_double_bound_pat_vars pmi));

fun is_sml_pmatch (pmi : pmatch_info) =
  (is_ocaml_pmatch pmi) andalso
  (null (#pmi_has_guards pmi));

val init_pmatch_info : pmatch_info = {
  pmi_is_well_formed            = false,
  pmi_ill_formed_rows           = [],
  pmi_has_free_pat_vars         = [],
  pmi_has_unused_pat_vars       = [],
  pmi_has_double_bound_pat_vars = [],
  pmi_has_guards                = [],
  pmi_has_lambda_in_pat         = [],
  pmi_has_non_contr_in_pat      = [],
  pmi_exhaustiveness_cond       = NONE
}

fun pmi_genupdate f1 f2 f3 f4 f5 f6 f7 f8 f9
  (pmi : pmatch_info) = ({
  pmi_is_well_formed            = f1 (#pmi_is_well_formed pmi),
  pmi_ill_formed_rows           = f2 (#pmi_ill_formed_rows pmi),
  pmi_has_free_pat_vars         = f3 (#pmi_has_free_pat_vars pmi),
  pmi_has_unused_pat_vars       = f4 (#pmi_has_unused_pat_vars pmi),
  pmi_has_double_bound_pat_vars = f5 (#pmi_has_double_bound_pat_vars pmi),
  pmi_has_guards                = f6 (#pmi_has_guards pmi),
  pmi_has_lambda_in_pat         = f7 (#pmi_has_lambda_in_pat pmi),
  pmi_has_non_contr_in_pat      = f8 (#pmi_has_non_contr_in_pat pmi),
  pmi_exhaustiveness_cond       = f9 (#pmi_exhaustiveness_cond pmi)
}:pmatch_info)

fun pmi_set_is_well_formed x =
    pmi_genupdate (K x) I I I I I I I I

fun pmi_add_ill_formed_row row_no =
    pmi_genupdate (K true) (cons row_no) I I I I I I I;

fun pmi_add_has_free_pat_vars row_no vars =
    pmi_genupdate I I (cons (row_no, vars)) I I I I I I;

fun pmi_add_has_unused_pat_vars row_no vars =
    pmi_genupdate I I I (cons (row_no, vars)) I I I I I;

fun pmi_add_has_double_bound_pat_vars row_no vars =
    pmi_genupdate I I I I (cons (row_no, vars)) I I I I;

fun pmi_add_has_guards row_no =
    pmi_genupdate I I I I I (cons row_no) I I I;

fun pmi_add_has_lambda_in_pat row_no =
    pmi_genupdate I I I I I I (cons row_no) I I;

fun pmi_add_has_non_contr_in_pat row_no terms =
    pmi_genupdate I I I I I I I (cons (row_no, terms)) I;

fun pmi_set_pmi_exhaustiveness_cond thm_opt =
    pmi_genupdate I I I I I I I I (K thm_opt);


local

  fun analyse_pat (ls : bool (* has lamdbda been seen *),
                   sv : term set (* set of all seen vars *),
                   msv : term set (* set of all vars seen more than once *),
                   sc : term set (* set of all seen constants *))
       t =
    if is_var t then let
         val (sv, msv) = if HOLset.member (sv, t) then
            (sv, HOLset.add (msv, t))
         else
            (HOLset.add (sv, t), msv)
      in (ls, sv, msv, sc)
    end else if (Literal.is_literal t orelse is_const t) then
      (ls, sv, msv, HOLset.add (sc,t))
    else if (is_abs t) then
      (true, sv, msv, sc)
    else if (is_comb t) then let
        val (t1, t2) = dest_comb t
        val (ls, sv, msv, sc) = analyse_pat (ls, sv, msv, sc) t1
        val (ls, sv, msv, sc) = analyse_pat (ls, sv, msv, sc) t2
      in
         (ls, sv, msv, sc)
      end
    else failwith "UNREACHABLE"


  fun analyse_row ((row_num, row),pmi) = let
    val (p_vars, p_body, g_body, _) =
      dest_PMATCH_ROW_ABS row

    (* check guard *)
    val pmi = if aconv g_body T then pmi else
                pmi_add_has_guards row_num pmi

    (* check pattern *)
    val vars_l = pairSyntax.strip_pair p_vars
    val vars = HOLset.fromList Term.compare vars_l
    val (ls, sv, msv, sc) = analyse_pat (false,
       HOLset.empty Term.compare,
       HOLset.empty Term.compare,
       HOLset.empty Term.compare) p_body

    (* Take care of unit vars *)
    val sv = case vars_l of
        [v] => if type_of v = oneSyntax.one_ty then
          HOLset.add (sv, v) else sv
      | _ => sv

    (* check lambda *)
    val pmi = if ls then
                pmi_add_has_lambda_in_pat row_num pmi
              else pmi

    (* check free_vars *)
    val fv = HOLset.difference (sv, vars)
    val pmi = if HOLset.isEmpty fv then pmi else
                (pmi_add_has_free_pat_vars row_num
                   (HOLset.listItems fv) pmi)

    (* check unused vars *)
    val uv = HOLset.difference (vars, sv)
    val pmi = if HOLset.isEmpty uv then pmi else
                (pmi_add_has_unused_pat_vars row_num
                   (HOLset.listItems uv) pmi)

    (* check double vars *)
    val dv = HOLset.intersection (msv, vars)
    val pmi = if HOLset.isEmpty dv then pmi else
                (pmi_add_has_double_bound_pat_vars row_num
                   (HOLset.listItems dv) pmi)

    (* check constructors vars *)
    val c_l = HOLset.listItems sc
    val nc_l = List.filter (fn c =>
       not (TypeBase.is_constructor c orelse Literal.is_literal c)) c_l
    val pmi = if null nc_l then pmi else
                (pmi_add_has_non_contr_in_pat row_num
                   nc_l pmi)
  in
    pmi
  end

in

fun analyse_pmatch try_exh t = let
  val (_, rows) = dest_PMATCH t
  val nrows = enumerate 0 rows
  val pmi = pmi_set_is_well_formed true init_pmatch_info
  val pmi = List.foldl analyse_row pmi nrows

  val pmi = (if (try_exh andalso is_ocaml_pmatch pmi) then
      pmi_set_pmi_exhaustiveness_cond (SOME (PMATCH_IS_EXHAUSTIVE_CONSEQ_CHECK t)) pmi else pmi) handle HOL_ERR _ => pmi

in
  pmi
end handle HOL_ERR _ => init_pmatch_info

end


end
