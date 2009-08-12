structure CooperShell :> CooperShell =
struct

open HolKernel boolLib integerTheory
     arithmeticTheory intSyntax int_arithTheory intReduce
     CooperSyntax CooperThms CooperMath;

val ERR = mk_HOL_ERR "CooperShell";
val lhand = rand o rator

(* Fix the grammar used by this file *)
structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars integer_grammars
end
open Parse

val simple_disj_congruence =
  tautLib.TAUT_PROVE (Term`!p q r. (~p ==> (q = r)) ==>
                                   (p \/ q = p \/ r)`)
val simple_conj_congruence =
  tautLib.TAUT_PROVE (Term`!p q r. (p ==> (q = r)) ==>
                                   (p /\ q = p /\ r)`)

fun congruential_simplification tm = let
  val (d1, d2) = dest_disj tm
in
  if is_disj d1 then
    REWR_CONV (GSYM DISJ_ASSOC) THENC congruential_simplification
  else if is_conj d1 then
    LAND_CONV congruential_simplification THENC
    RAND_CONV congruential_simplification
  else if d1 = true_tm then
    K (SPEC d2 T_or_l)
  else if d1 = false_tm then
    K (SPEC d2 F_or_l)
  else let
      val notd1_t = mk_neg d1
      val notd1_thm = ASSUME notd1_t
      val notd1 =
          if is_neg d1 then
            EQT_INTRO (CONV_RULE (REWR_CONV NOT_NOT_P) notd1_thm)
          else EQF_INTRO (notd1_thm)
      val d2_rewritten = SOME (DISCH notd1_t (REWRITE_CONV [notd1] d2))
          handle UNCHANGED => NONE
  in
      case d2_rewritten of
        NONE => RAND_CONV congruential_simplification
      | SOME d2thm =>
        K (MATCH_MP simple_disj_congruence d2thm) THENC
        (REWR_CONV T_or_r ORELSEC REWR_CONV F_or_r ORELSEC
         RAND_CONV congruential_simplification)
  end
end tm handle HOL_ERR _ => let
  val (c1, c2) = dest_conj tm
in
  if is_conj c1 then
    REWR_CONV (GSYM CONJ_ASSOC) THENC congruential_simplification
  else if is_disj c1 then
    LAND_CONV congruential_simplification THENC
    RAND_CONV congruential_simplification
  else if c1 = true_tm then
    K (SPEC c2 T_and_l)
  else if c1 =  false_tm then
    K (SPEC c2 F_and_l)
  else let
      val c2_rewritten =
          SOME (DISCH c1 (REWRITE_CONV [EQT_INTRO (ASSUME c1)] c2))
          handle UNCHANGED => NONE
    in
      case c2_rewritten of
        NONE => RAND_CONV congruential_simplification
      | SOME th =>
        K (MATCH_MP simple_conj_congruence th) THENC
        (REWR_CONV T_and_r ORELSEC REWR_CONV F_and_r ORELSEC
         RAND_CONV congruential_simplification)
  end
end tm handle HOL_ERR _ =>
  if is_neg tm then RAND_CONV congruential_simplification tm
  else ALL_CONV tm

val unwind_constraint = UNCONSTRAIN THENC resquan_remove

val p6_step = prove(
  ``(?x:int. K (lo < x /\ x <= hi) x /\ P x) =
    lo < hi /\ (P hi \/ (?x:int. K (lo < x /\ x <= hi - 1) x /\ P x))``,
  REWRITE_TAC [combinTheory.K_THM, LEFT_AND_OVER_OR] THEN
  EQ_TAC THENL [
    CONV_TAC
      (LAND_CONV (ONCE_REWRITE_CONV [restricted_quantification_simp])) THEN
    STRIP_TAC THENL [
      FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC [],
      ASM_REWRITE_TAC [] THEN DISJ2_TAC THEN
      Q.EXISTS_TAC `x` THEN ASM_REWRITE_TAC []
    ],
    STRIP_TAC THENL [
      Q.EXISTS_TAC `hi` THEN ASM_REWRITE_TAC [INT_LE_REFL],
      ONCE_REWRITE_TAC [restricted_quantification_simp] THEN
      Q.EXISTS_TAC `x` THEN  ASM_REWRITE_TAC []
    ]
  ]);

fun p6_recurse tm = let
  (* tm of form ?x. K (lo < x /\ x <= hi) x /\ P x *)
in
  REWR_CONV p6_step THENC
  LAND_CONV REDUCE_CONV THENC
  (REWR_CONV F_and_l ORELSEC
   (REWR_CONV T_and_l THENC
    LAND_CONV BETA_CONV THENC
    RAND_CONV (BINDER_CONV (* under ?x. *)
               (LAND_CONV (* into K (..) x *)
                (LAND_CONV (* into lo < x /\ x <= hi - 1 *)
                 (RAND_CONV REDUCE_CONV))) THENC
               p6_recurse)))
end tm



fun phase6_CONV tm = let
  (* succeeds on disjuncts of the form
        ?x. K (lo < x /\ x <= hi) x /\ P x
     and converts these to
        P (lo + 1) \/ P (lo + 2) \/ ... P hi
     where each argument to P is actually a real numeral (not an expression)
  *)
  val (v, _) = dest_exists tm
in
  BINDER_CONV (RAND_CONV (UNBETA_CONV v)) THENC
  p6_recurse THENC PURE_REWRITE_CONV [F_or_r]
end tm

(*
val phase6_CONV = Profile.profile "phase6" phase6_CONV
*)

fun vphase6_CONV tm = let
  (* as above, but works over the constraint attached to v, not the one
     immediately under the binder *)
  val (v, body) = dest_exists tm
in
  BINDER_CONV (move_conj_left (is_vconstraint v)) THENC
  phase6_CONV
end tm;

fun elim_vars_round_r tm = let
  val (l,r) = dest_eq tm
    handle HOL_ERR _ => dest_less tm
  val lvars = filter (not o null o free_vars) (strip_plus l)
  val rvars = filter (not o null o free_vars) (strip_plus r)
in
  case intersect lvars rvars of
    [] => NO_CONV
  | (h::_) => phase2_CONV (hd (free_vars h))
end tm


val obvious_improvements =
  ADDITIVE_TERMS_CONV (TRY_CONV collect_additive_consts) THENC
  STRIP_QUANT_CONV
    (BLEAF_CONV (op THENC) (elim_vars_round_r ORELSEC
                             TRY_CONV check_divides) THENC
     REDUCE_CONV)

fun do_equality_simplifications tm = let
  (* term is existentially quantified.  May contain leaf terms of the form
     v = e, where v is the variable quantified.  If there is such a term at
     the top level of conjuncts, then use UNWIND_CONV to eliminate the
     quantifier entirely, otherwise, descend the term looking for such
     terms in the middle of conjunctions and eliminate the equality from the
     neighbouring conjuncts. *)
  val (bvar, body) = dest_exists tm
  fun eq_term tm = is_eq tm andalso lhs tm = bvar
  fun neq_term t = eq_term (dest_neg t) handle HOL_ERR _ => false

  fun reveal_eq tm = let
    (* tm is a "conjunctive" term, in which there is an equality of the
       form (bvar = e).

       Our mission, should we choose to accept it, is to selectively rewrite
       with de-morgan's thm to reveal the tm to  be of the form:
           P /\ Q /\ (bvar = e) /\ R
    *)
    val (c1,c2) = dest_conj tm
    (* easy case because the top level operator is already correct *)
    val subconv =
      if List.exists eq_term (cpstrip_conj c1) then LAND_CONV
      else RAND_CONV
  in
    subconv reveal_eq tm
  end handle HOL_ERR _ => let
    val tm0 = dest_neg tm
  in
    if is_neg tm0 then
      (REWR_CONV NOT_NOT_P THENC reveal_eq) tm
    else (* must be a disjunction *)
      (REWR_CONV NOT_OR THENC reveal_eq) tm
  end handle HOL_ERR _ => ALL_CONV tm

  fun reveal_neq tm = let
    (* tm is a "disjunctive" term in which there is a negated equality *)
    val (d1,d2) = dest_disj tm
    val subconv = if List.exists neq_term (cpstrip_disj d1) then LAND_CONV
                  else RAND_CONV
  in
    subconv reveal_neq tm
  end handle HOL_ERR _ => let
    val tm0 = dest_neg tm
  in
    if is_neg tm0 then
      (REWR_CONV NOT_NOT_P THENC reveal_neq) tm
    else if is_conj tm0 then
      (REWR_CONV NOT_AND THENC reveal_neq) tm
    else ALL_CONV tm
  end handle HOL_ERR _ => ALL_CONV tm

  fun descend_and_eliminate tm =
    if is_conj tm then
      if List.exists eq_term (cpstrip_conj tm) then let
        val revealed = reveal_eq tm
        val revealed_t = rhs (concl revealed)
        val (eqt, rest) = Lib.pluck eq_term (strip_conj revealed_t)
        val rearranged_t = mk_conj(eqt, list_mk_conj rest)
        val rearranged = EQT_ELIM (AC_CONV (CONJ_ASSOC, CONJ_COMM)
                                   (mk_eq(revealed_t, rearranged_t)))
        val eliminated =
          (RAND_CONV (UNBETA_CONV bvar) THENC
           REWR_CONV CONJ_EQ_ELIM THENC
           RAND_CONV BETA_CONV) rearranged_t
      in
        TRANS (TRANS revealed rearranged) eliminated
      end
      else
        cpEVERY_CONJ_CONV descend_and_eliminate tm
    else if is_disj tm then
      if List.exists neq_term (cpstrip_disj tm) then let
        val revealed = reveal_neq tm
        val revealed_t = rhs (concl revealed)
        val (eqt, rest) = Lib.pluck neq_term (strip_disj revealed_t)
        val rearranged_t = mk_disj(eqt, list_mk_disj rest)
        val rearranged = EQT_ELIM (AC_CONV (DISJ_ASSOC, DISJ_COMM)
                                   (mk_eq(revealed_t, rearranged_t)))
        val eliminated =
          (RAND_CONV (UNBETA_CONV bvar) THENC
           REWR_CONV DISJ_NEQ_ELIM THENC
           RAND_CONV BETA_CONV) rearranged_t
      in
        TRANS (TRANS revealed rearranged) eliminated
      end
      else
        cpEVERY_DISJ_CONV descend_and_eliminate tm
    else if is_neg tm then
      RAND_CONV descend_and_eliminate tm
    else ALL_CONV tm
in
  if List.exists eq_term (cpstrip_conj body) then
    BINDER_CONV reveal_eq THENC Unwind.UNWIND_EXISTS_CONV
  else
    BINDER_CONV descend_and_eliminate
end tm

fun reveal_a_disj tm =
  if is_disj tm then ALL_CONV tm
  else let
    val tm0 = dest_neg tm
  in
    if is_conj tm0 then REWR_CONV NOT_AND tm
    else (REWR_CONV NOT_NOT_P THENC reveal_a_disj) tm
  end



open CooperCore
local
  fun stop_if_exelim tm =
    if is_exists tm then NO_CONV tm
    else REDUCE_CONV tm
in
  fun eliminate_existential tm = let
    val (bvar, body) = dest_exists tm
      handle HOL_ERR _ =>
        raise ERR "eliminate_existential" "term not an exists"
    val base_case =
      BINDER_CONV (phase2_CONV bvar THENC
                   REPEATC (CHANGED_CONV congruential_simplification) THENC
                   REDUCE_CONV) THENC
      ((REWR_CONV EXISTS_SIMP THENC REWRITE_CONV []) ORELSEC
       (phase3_CONV THENC do_equality_simplifications THENC
        (stop_if_exelim ORELSEC
         (phase4_CONV THENC phase5_CONV))))
  in
    if cpis_disj body then
      BINDER_CONV reveal_a_disj THENC EXISTS_OR_CONV THENC
      (RAND_CONV eliminate_existential) THENC
      (LAND_CONV eliminate_existential)
    else
      base_case THENC EVERY_DISJ_CONV obvious_improvements
  end tm
end

val eliminate_existential_entirely =
    (* used to eliminate an existential, and to lose any constraint *)
    (* existentials underneath; basically eliminate_existential followed *)
    (* by phase 6 *)
    eliminate_existential THENC
    EVERY_DISJ_CONV
       (TRY_CONV phase6_CONV THENC
        (* variables substituted in might result in ground
           multiplication terms *)
        REDUCE_CONV THENC obvious_improvements)


fun eliminate_quantifier tm = let
(* assume that there are no quantifiers below the one we're eliminating *)
in
  if is_forall tm then
    flip_forall THENC RAND_CONV eliminate_existential_entirely
  else if is_exists tm then
    eliminate_existential_entirely
  else if is_exists1 tm then
    HO_REWR_CONV cpEU_THM THENC
    RAND_CONV (BINDER_CONV eliminate_quantifier THENC
               eliminate_quantifier) THENC
    RATOR_CONV (RAND_CONV eliminate_quantifier)
  else
    raise ERR "eliminate_quantifier"
      "Not a forall or an exists or a unique exists"
end tm

fun find_low_quantifier tm = let
  fun underc g f =
    case f of
      NONE => NONE
    | SOME f' => SOME (g o f')
in
  if (is_forall tm orelse is_exists tm orelse is_exists1 tm) then
    case find_low_quantifier (#2 (dest_abs (#2 (dest_comb tm)))) of
      NONE => SOME I
    | x => underc BINDER_CONV x
  else if is_comb tm then
    case find_low_quantifier (rand tm) of
      NONE => underc RATOR_CONV (find_low_quantifier (rator tm))
    | x => underc RAND_CONV x
  else
    NONE
end

fun myfind f [] = NONE
  | myfind f (h::t) = case f h of NONE => myfind f t | x => x

fun find_equality tm = let
  (* if there is an equality term as a conjunct underneath any number of
     disjuncts, then return one of the free variables of that equality *)
  fun check_conj tm =
    if is_eq tm then let
      val fvs = free_vars tm
    in
      if not (null fvs) then SOME (hd fvs) else NONE
    end else NONE
in
  myfind check_conj (cpstrip_conj tm)
end

fun best_var vars tm = let
  (* Finds the variable in the list vars that occurs in term tm so as
     to minimise the number of splits necessary if that variable was
     chosen to eliminate.  The rating given to a variable is
     the minimum of its a and b-var counts.

     Weights variables slightly higher for appearing earlier in the
     list vars, this means that unnecessary swapping of existential
     variables is avoided. Assume that all variables in term and all
     the variables in the list are of type int.  Return SOME n, or
     NONE if vars is the empty list *)
  fun assess_leaf v negp t = let
    (* returns a-count and b-count for v in term t, with negp true if
       term is under a negation *)
    val (f, args) = strip_comb t
    val (arg1, arg2) = (hd args, hd (tl args))
    val c1 = sum_var_coeffs v arg1
    val c2 = sum_var_coeffs v arg2
    open Arbint
  in
    if c1 = c2 then (zero,zero)
    else if same_const f less_tm then
      if negp then
        if Arbint.<(c1, c2) then (one,zero) else (zero,one)
      else
        if Arbint.<(c1, c2) then (zero,one) else (one,zero)
    else (one,one)  (* must be an equality *)
  end
  fun assess negp map t = let
    val (f, args) = strip_comb t
  in
    if same_const f boolSyntax.negation then assess (not negp) map (hd args)
    else if same_const f boolSyntax.conjunction orelse
            same_const f boolSyntax.disjunction
    then
      assess negp (assess negp map (hd args)) (hd (tl args))
    else if is_const t then
      (* happens when we have a vacuous quantification over true or false *)
      map
    else let
        fun foldthis (v, map) = let
          open Arbint
          val (a,b) = assess_leaf v negp t
          val (a0,b0) = Binarymap.find(map, v)
              handle Binarymap.NotFound => (zero,zero)
        in
          Binarymap.insert(map, v, (a + a0, b + b0))
        end
      in
        List.foldl foldthis map vars
      end
  end
  val initial_map = Binarymap.mkDict Term.compare
in
  case vars of
    [] => NONE
  | [x] => SOME x
  | (v::vs) => let
      val final_map = assess false initial_map tm
      val start = (v, Arbint.min(Binarymap.find(final_map, v))
                      handle Binarymap.NotFound => Arbint.zero)
      fun findmin (v, acc as (minvar, minc)) = let
        val vc = Arbint.min(Binarymap.find(final_map, v))
                            handle Binarymap.NotFound => Arbint.zero
      in
        if Arbint.<=(vc, minc) then (v, vc) else acc
      end
    in
      SOME (#1 (List.foldl findmin start vs))
    end
end



fun pull_last_exists_to_top tm = let
  val (v, body) = dest_exists tm
in
  if is_exists body then
    (BINDER_CONV pull_last_exists_to_top THENC
     SWAP_VARS_CONV) tm
  else
    ALL_CONV tm
end

fun push_nthvar_to_bot n tm =
    if n <= 0 then TRY_CONV (SWAP_VARS_CONV THENC
                             BINDER_CONV (push_nthvar_to_bot 0)) tm
    else BINDER_CONV (push_nthvar_to_bot (n - 1)) tm

fun listlex_compare c (l1, l2) =
    (* do a lexicographic comparison of list1 and list2, using c to compare
       their elements *)
    case (l1, l2) of
      ([], []) => EQUAL
    | (h::t, []) => GREATER
    | ([], h::t) => LESS
    | (h1::t1, h2::t2) =>
      case c(h1, h2) of
        EQUAL => listlex_compare c (t1, t2)
      | x => x

fun find_dup c l =
    (* l is a sorted list; find the first duplicated element, according to c *)
    case l of
      [] => NONE
    | [_] => NONE
    | (h1 :: (tail as (h2 :: t))) => if c(h1, h2) = EQUAL then SOME h1
                                     else find_dup c tail

val do_muls = ONCE_DEPTH_CONV LINEAR_MULT

fun find_triangle_eliminable vset dcsts csts = let
  (* pick an element of vset to minimise the blow-up after doing a
     Cooper triangle elimination on the two dcsts The list csts is of
     range constraints from the problem.

     Recall that
       m | ax + b /\ n | ux + v
     gets turned into
       mn | dx + vmp + bnq /\ d | av - ub
     where
       d = gcd(mu, an) = pum + qan

     If vset has two elements, then the second conjunct of the result will
     be a divides constraint over just one variable, and we can pick the
     variable that results in the best performance.  It's not clear what
     should be done if there are more variables.

     For the moment, and this is probably a god-awful HACK, just return
     the hd of the list vset.
  *)
in
  if length vset > 2 then (hd vset, hd (tl vset))
  else let
      open Arbint
      val dcst1 = hd dcsts
      val dcst2 = hd (tl dcsts)
      val (m, rhs1) = dest_divides dcst1
      val m_i = int_of_term m
      val (n, rhs2) = dest_divides dcst2
      val n_i = int_of_term n
      fun calculate_score v_to_go v_to_remain = let
        val a_i = abs (sum_var_coeffs v_to_go rhs1)
        val u_i = abs (sum_var_coeffs v_to_go rhs2)
        val d0_i = gcd(m_i, n_i)
        val b_i = sum_var_coeffs v_to_remain rhs1
        val v_i = sum_var_coeffs v_to_remain rhs2
        val remain0_i = a_i * v_i - u_i * b_i
        val divide_by = gcd(d0_i, abs remain0_i)
        val remain_i = remain0_i div divide_by
        val d_i = d0_i div divide_by
        val cst = valOf (List.find (is_vconstraint v_to_remain) csts)
      in
        constraint_size cst div d_i
      end
      val v1 = hd vset
      val v2 = hd (tl vset)
      val v1_score = calculate_score v1 v2
      val v2_score = calculate_score v2 v1
    in
      if v1_score > v2_score then (v2,v1) else (v1,v2)
    end
end






fun finish_pure_goal1 tm = let
  (* tm is of the form
        ?x1 .. xn. K1 /\ K2 /\ .. /\ Kn /\ P (x1..xn) /\
                   c1 | ... /\ c2 | ...
     where the Ki's are constraints (one per existential variable).
     In this stage of the process we try to do "delta elimination" to
     avoid having to consider all of the possibilities in the
     constraints.  Sometimes this is not possible, but the effect of this
     function is to make one step of progress regardless.

     The ideal situation is when one of the ex. variables is mentioned just
     once in a divisibility term's right-hand-side.  If this situation holds
     we can use simplify_constrained_disjunct to make progress.  Otherwise,
     if two divisibility constraints exist with the same set of free
     variables on the right hand side, we can make progress by using
     Cooper's first lemma to change this, producing two new divisibility
     constraints, one of which has one fewer variable than the original.

     If neither situation holds, then we have no choice but to expand
     one of the variables, as per phase6.  We pick the variable with the
     smallest range.
  *)
  val (vars, body) = strip_exists tm
  val (constraints, nonconstraints) =
      partition is_constraint (cpstrip_conj body)
  val (div_constraints, others) = partition is_divides nonconstraints
  val divc_rhses = map (#2 o dest_divides) div_constraints
  val canonicalise_varsets = Listsort.sort Term.compare
  fun free_vars' t = (t, free_vars t)
  fun nzero_coeffs (t, vlist) =
      filter (fn v => sum_var_coeffs v t <> Arbint.zero) vlist
  val div_varsets =
      map (canonicalise_varsets o nzero_coeffs o free_vars') divc_rhses
in
  case List.find (fn lst => length lst = 1) div_varsets of
    SOME vs => let
      (* found a singleton divisibility constraint *)
      val v = hd vs
    in
      push_nthvar_to_bot (index (equal v) vars) THENC
      STRIP_QUANT_CONV (phase2_CONV v) THENC
      LAST_EXISTS_CONV simplify_constrained_disjunct THENC
      do_muls
    end
  | NONE => let
      val vset_compare = listlex_compare Term.compare
      val sorted_vsets = Listsort.sort vset_compare div_varsets
    in
      case find_dup vset_compare sorted_vsets of
        SOME vset => let
          fun my_constraint tm =
              is_divides tm andalso
              canonicalise_varsets (free_vars (#2 (dest_divides tm))) = vset
          val (var_to_eliminate, var_to_keep) =
              find_triangle_eliminable
                vset
                (List.take(List.filter my_constraint div_constraints, 2))
                constraints
        in
          STRIP_QUANT_CONV
            (move_conj_left my_constraint THENC
             RAND_CONV (move_conj_left my_constraint) THENC
             REWR_CONV CONJ_ASSOC THENC
             LAND_CONV (phase2_CONV var_to_eliminate THENC
                        REWRITE_CONV [GSYM INT_ADD_ASSOC] THENC
                        elim_paired_divides THENC
                        phase1_CONV THENC phase2_CONV var_to_keep THENC
                        BINOP_CONV (TRY_CONV check_divides) THENC
                        REWRITE_CONV [INT_DIVIDES_1]))
        end
      | NONE => let
          (* look for constraint with least range *)
          fun min (c_tm, acc as (accv, acci)) = let
            val i = constraint_size c_tm
          in
            if Arbint.<(i,acci) then (constraint_var c_tm, i) else acc
          end
          val init = let val c = hd constraints
                     in (constraint_var c, constraint_size c)
                     end
          val (minv, _) = List.foldl min init (tl constraints)
        in
          push_nthvar_to_bot (index (equal minv) vars) THENC
          LAST_EXISTS_CONV vphase6_CONV THENC
          push_in_exists
        end
    end
end tm

fun finish_pure_goal tm =
    if is_exists tm then
      ((REWR_CONV EXISTS_SIMP ORELSEC finish_pure_goal1) THENC
       EVERY_DISJ_CONV (obvious_improvements THENC finish_pure_goal)) tm
    else REDUCE_CONV tm


(*
  val tm0 = ``?w. ((y = 2 * w) \/ (y = 2 * w + 1)) /\ x <= w /\ w < z``
  val tm = rhs (concl (phase1_CONV tm0))

  val tm0 =
    ``!x y z. 2 * x < y /\ y < 2 * z ==>
   (~(1 * y + ~1 < 2 * x) /\ 1 * y + ~1 < 2 * z /\
        2 int_divides 1 * y + ~1 \/
        ~(1 * y < 2 * x) /\ 1 * y < 2 * z /\ 2 int_divides 1 * y) \/
       ~(1 * y + ~1 < 2 * x) /\ 1 * y + ~1 < 2 * z /\
       2 int_divides 1 * y + ~1 \/
       ((2 * z + ~2 = 1 * y) \/ (2 * z + ~2 = 1 * y + ~1)) /\
       ~(2 * z + ~2 < 2 * x)``
 val tm = rand (rhs (concl ((phase1_CONV THENC flip_foralls) tm0)))

val tm0 =
    ``!x.
        0 <= x ==>
        !x'.
          0 <= x' ==>
          x' <= x ==>
          !x''.
            0 <= x'' ==>
            (~(x <= x') \/ (x'' + x = x'' + x') \/
             x'' <= 0 /\ x'' + x' <= x) /\
            (x <= x' \/
             (~(x'' + x' <= x) \/ (x'' + x' = x) \/ x'' <= 0 /\ x <= x') /\
             (x'' + x' <= x \/ (x'' + (x + x') = x + (x'' + x')) \/
              x'' <= 0 /\ x + (x'' + x') <= x + x')) \/
            (x'' + x' <= x \/ x'' <= 0) /\ x'' + x' <= x + 0``

val tm = rand (rhs (concl ((phase1_CONV THENC move_quants_up THENC
                            flip_foralls) tm0)))


*)

fun pure_goal0 tm = let
  (* pure_goal is called on those goals that have all existential
     quantifiers; these are assumed to be at the head of the term  *)
  val (vars, body) = strip_exists tm
  fun pull_out_and_recurse n tm = let
    (* tm is of the form    ?x1 .. xn. p *)
    (* where p may or may not have an existential quantifier *)
    (* if there is a quantifier over p, want to pull it out to the front *)
    (* of the list and then recurse just underneath it, otherwise recurse *)
    (* immediately *)
    val (vars, body) = strip_exists tm
  in
    if length vars = n then pure_goal0 tm
    else (pull_last_exists_to_top THENC BINDER_CONV pure_goal0) tm
  end
in
  if null vars then REDUCE_CONV
  else if cpis_disj body then
    STRIP_QUANT_CONV reveal_a_disj THENC
    push_in_exists THENC BINOP_CONV pure_goal0 THENC
    REDUCE_CONV
  else let
    val next_var =
      case find_equality body of
        NONE => valOf (best_var vars body)
      | SOME v => v
  in
      push_nthvar_to_bot (index (equal next_var) vars) THENC
      LAST_EXISTS_CONV eliminate_existential THENC
      TRY_CONV push_in_exists THENC
      EVERY_DISJ_CONV (pull_out_and_recurse (length vars - 1) THENC
                       TRY_CONV push_in_exists)
  end
end tm

(*
val pure_goal0 = Profile.profile "pure_goal0" pure_goal0
val finish_pure_goal = Profile.profile "finish_pure_goal" finish_pure_goal
*)

val pure_goal = pure_goal0 THENC EVERY_DISJ_CONV finish_pure_goal THENC
                REDUCE_CONV

val tm100 = term_of_int (Arbint.fromInt 100)
fun counter_example tm = let
  open seqmonad
  infix >- >> ++
  fun rule f th = (seq.result (f th, ())) handle HOL_ERR _ => seq.empty
  fun test th =
    if (concl th = false_tm) then
      seq.result(EQF_INTRO (NOT_INTRO (DISCH tm th)),())
    else seq.empty
  fun spec n th = let
  in
    if is_forall (concl th) then
      if n > 0 then
        ((rule (SPEC zero_tm) ++ rule (SPEC tm100)) >>
         spec (n - 1))
      else rule (SPEC one_tm) >> spec (n - 1)
    else
      rule (CONV_RULE REDUCE_CONV) >> test
  end th
in
  case seq.cases (spec 5 (ASSUME tm)) of
    NONE => NO_CONV tm
  | SOME ((th,()),_) => th
end


fun decide_pure_presburger_term tm = let
  (* no free variables allowed *)
  val phase0_CONV =
    (* rewrites out conditional expression terms *)
    TOP_DEPTH_CONV (REWR_CONV COND_EXPAND ORELSEC
                    REWR_CONV COND_RATOR ORELSEC
                    IntDP_Munge.NBOOL_COND_RAND_CONV ORELSEC
                    IntDP_Munge.COND_ABS_CONV)

  fun mainwork tm = let
  in
    case find_low_quantifier tm of
      NONE => REDUCE_CONV
    | SOME f =>
        f eliminate_quantifier THENC
        REWRITE_CONV []
  end tm
  fun strategy tm =
    case goal_qtype tm of
      NEITHER => (mainwork THENC strategy) tm
    | EITHER => REDUCE_CONV tm
    | qsUNIV =>
        (move_quants_up THENC
         ((* counter_example ORELSEC *)
          (flip_foralls THENC
           RAND_CONV pure_goal THENC REDUCE_CONV))) tm
    | qsEXISTS => (move_quants_up THENC pure_goal) tm
in
  phase0_CONV THENC phase1_CONV THENC strategy
end tm

(* the following is useful in debugging the above; given an f, the
   function term_at_f will return the term "living" at f, as long as there
   are no terms of the form (I tm) in the original.
     local fun I_CONV tm = SYM (ISPEC tm combinTheory.I_THM)
           val I_tm = Term`I:bool->bool b`
     in
       fun term_at_f f tm =
         rand (find_term (can (match_term I_tm)) (rhs (concl (f I_CONV tm))))
     end
   another useful function is this, which allows for the elimination
   of the specified number of quantifiers:
     fun elim_nqs n tm = let
     in
       if n <= 0 then ALL_CONV
       else
          case find_low_quantifier tm of
            NONE => ALL_CONV
          | SOME f => f eliminate_quantifier THENC REWRITE_CONV [] THENC
                      elim_nqs (n - 1)
     end tm

*)

end
