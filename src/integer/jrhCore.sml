structure jrhCore :> jrhCore =
struct

open HolKernel boolLib integerTheory
     arithmeticTheory intSyntax int_arithTheory intSimps;

open CooperSyntax CooperThms CooperMath
open Profile
open DeepSyntaxTheory;

val lhand = rand o rator
val collect_additive_consts = profile "additive_consts" collect_additive_consts

val ERR = mk_HOL_ERR "Cooper";

(* Fix the grammar used by this file *)
structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars DeepSyntaxTheory.DeepSyntax_grammars
end
open Parse

val REWRITE_CONV = GEN_REWRITE_CONV Conv.TOP_DEPTH_CONV bool_rewrites


val tac = REWRITE_TAC [eval_form_def, Aset_def, Bset_def]
val conjn_rwt = prove(``!f1 f2 x. eval_form f1 x /\ eval_form f2 x =
                                  eval_form (Conjn f1 f2) x``, tac)
val disjn_rwt = prove(``!f1 f2 x. eval_form f1 x \/ eval_form f2 x =
                                  eval_form (Disjn f1 f2) x``, tac)
val negn_rwt = prove(``!f x. ~eval_form f x = eval_form (Negn f) x``, tac);
val unrelated_rwt = prove(``!b x. b = eval_form (UnrelatedBool b) x``, tac);
val binop_rwt_CONV = REWR_CONV conjn_rwt ORELSEC REWR_CONV disjn_rwt

val var_right_rwt = prove(
  ``!i x. (i < x = eval_form (LTx i) x) /\
          (i int_divides x = eval_form (xDivided i 0) x)``,
  REWRITE_TAC [eval_form_def, INT_ADD_RID]);
val var_nright_rwt = prove(
  ``!i1 i2 x. ((x = i1) = eval_form (xEQ i1) x) /\
              (x < i1 = eval_form (xLT i1) x) /\
              (i1 int_divides x + i2 = eval_form (xDivided i1 i2) x)``,
  tac);

fun convert_to_embedded_syntax tm = let
  (* tm is of form ?x. ..., were x is always bare in the ... *)
  val (var, body) = dest_exists tm
  fun recurse tm =
      if not (mem var (free_vars tm)) then
        SPECL [tm, var] unrelated_rwt
      else let
          val (c1, c2) = dest_conj tm handle HOL_ERR _ => dest_disj tm
          val eval1 = recurse c1
          (* i.e., (|- c1 = eval_form f1 x, |- Aset pos f1 = ...,
                    |- Bset pos f1 = ..., lcm1) *)
          val eval2 = recurse c2
          val eval = MK_COMB (AP_TERM (rator (rator tm)) eval1, eval2)
          (* i.e., c1 /\ c2 = eval_form f1 x /\ eval_form f2 x *)
        in
          TRANS eval (binop_rwt_CONV (rand (concl eval)))
        end
          handle HOL_ERR _ => let
                   val t0 = dest_neg tm
                   val eval0 = recurse t0
                   val eval = AP_TERM (rator tm) eval0
                 in
                   TRANS eval (REWR_CONV negn_rwt (rand (concl eval)))
                 end handle HOL_ERR _ =>
                            if rand tm = var then
                              REWRITE_CONV [var_right_rwt] tm
                            else
                              REWRITE_CONV [var_nright_rwt] tm
in
  EXISTS_EQ var (recurse body)
end


fun form_to_lcm var tm = let
  fun recurse acc tm =
    if not (mem var (free_vars tm)) then acc
    else let
        val (l,r) = dest_disj tm handle HOL_ERR _ => dest_conj tm
      in
        recurse (recurse acc l) r
      end handle HOL_ERR _ =>
                 if is_neg tm then recurse acc (rand tm)
                 else if is_divides tm then
                   lcm (int_of_term (rand (rator tm)), acc)
                 else acc
in
  recurse Arbint.one tm
end

val alldivide_t = ``alldivide``
fun prove_alldivide f d =
    EQT_ELIM ((REWRITE_CONV [alldivide_def] THENC REDUCE_CONV)
                (list_mk_comb(alldivide_t, [f,d])))


fun phase4_CONV tm = let
  val (var, body) = dest_exists tm
  val eval_thm = convert_to_embedded_syntax tm
  val f_t = rand (rator (#2 (dest_exists (rand (concl eval_thm)))))
  val lcm_i = form_to_lcm var body
  val lcm_t = term_of_int lcm_i
  val zero_lt_lcm = EQT_ELIM (REDUCE_CONV (mk_less(zero_tm, lcm_t)))
  val alldiv_th = prove_alldivide f_t lcm_t
  (* count a and b terms, also pair each count with the total number of free
     variables in these terms *)
  fun docount pos (acc as (ai as (a, afv), bi as (b, bfv))) tm =
      if not (mem var (free_vars tm)) then acc
      else let
          val (l,r) = dest_disj tm handle HOL_ERR _ => dest_conj tm
        in
          docount pos (docount pos acc l) r
        end handle HOL_ERR _ => let
          val t0 = dest_neg tm
        in
          docount (not pos) acc t0
        end handle HOL_ERR _ => let
          val (l,r) = dest_less tm
        in
          if (pos = (l = var)) then
            ((a + 1, afv + length (free_vars r)), bi)
          else
            (ai, (b + 1, bfv + length (free_vars l)))
        end handle HOL_ERR _ => (* must be equality or divides, neither
                                   has any effect on contest *) acc
  val ((ai,afv), (bi,bfv)) = docount true ((0,0), (0,0)) body
  val qe_thm =
      case Int.compare(ai,bi) of
        LESS => posinf_exoriginal_eq_rhs
      | EQUAL => if afv < bfv then posinf_exoriginal_eq_rhs
                 else neginf_exoriginal_eq_rhs
      | GREATER => neginf_exoriginal_eq_rhs
  val eliminated_th = MATCH_MP qe_thm (CONJ alldiv_th zero_lt_lcm)
in
  TRANS eval_thm eliminated_th
end

val phase4_CONV = profile "phase4" phase4_CONV

val bset_thms = CONJUNCTS in_bset
val aset_thms = CONJUNCTS in_aset
fun in_set_CONV tm = let
  val (v, body) = dest_exists tm
  val (in_t, _) = dest_conj body
  val (set_conjn::set_disjn::set_negnt::set_negnf::rest) =
      if #1 (dest_const (#1 (strip_comb (rand in_t)))) = "Aset" then aset_thms
      else bset_thms

  fun recurse tm = let
    val (v, body) = dest_exists tm
    val (in_t, _) = dest_conj body
    val f = rand (rand in_t)
  in
    case (#1 (dest_const (#1 (strip_comb f)))) of
      "Conjn" => REWR_CONV set_conjn THENC BINOP_CONV recurse
    | "Disjn" => REWR_CONV set_disjn THENC BINOP_CONV recurse
    | "Negn" => FIRST_CONV (map REWR_CONV [set_negnf, set_negnt]) THENC
                recurse
    | _ => FIRST_CONV (map REWR_CONV rest)
  end tm
in
  recurse tm
end



val eval_f_CONV = REWRITE_CONV [eval_form_def]

fun elim_bterms tm = let
  (* tm is of form
        ?b. (b IN Xset pos f /\ K ... j) /\ ....
     or
        ?b. b IN Xset pos f /\ ...
  *)
  val (var, body) = dest_exists tm
  val initially = if is_conj (lhand body) then REWR_CONV (GSYM CONJ_ASSOC)
                  else ALL_CONV
in
  BINDER_CONV (initially THENC
               profile "eb.eval" eval_f_CONV THENC
               profile "eb.abs" (RAND_CONV (UNBETA_CONV var))) THENC
  profile "eb.in_set" in_set_CONV THENC
  profile "eb.beta" (EVERY_DISJ_CONV (TRY_CONV BETA_CONV))
end tm

val eval_form_neginf = prove(
  ``(eval_form (neginf (Conjn f1 f2)) x = eval_form (neginf f1) x /\
                                          eval_form (neginf f2) x) /\
    (eval_form (neginf (Disjn f1 f2)) x = eval_form (neginf f1) x \/
                                          eval_form (neginf f2) x) /\
    (eval_form (neginf (Negn f)) x = ~eval_form (neginf f) x) /\
    (eval_form (neginf (UnrelatedBool b)) x = b) /\
    (eval_form (neginf (xLT i)) x = T) /\
    (eval_form (neginf (LTx i)) x = F) /\
    (eval_form (neginf (xEQ i)) x = F) /\
    (eval_form (neginf (xDivided i1 i2)) x = i1 int_divides x + i2)``,
  REWRITE_TAC [eval_form_def, neginf_def]);
val eval_form_posinf = prove(
  ``(eval_form (posinf (Conjn f1 f2)) x = eval_form (posinf f1) x /\
                                          eval_form (posinf f2) x) /\
    (eval_form (posinf (Disjn f1 f2)) x = eval_form (posinf f1) x \/
                                          eval_form (posinf f2) x) /\
    (eval_form (posinf (Negn f)) x = ~eval_form (posinf f) x) /\
    (eval_form (posinf (UnrelatedBool b)) x = b) /\
    (eval_form (posinf (xLT i)) x = F) /\
    (eval_form (posinf (LTx i)) x = T) /\
    (eval_form (posinf (xEQ i)) x = F) /\
    (eval_form (posinf (xDivided i1 i2)) x = i1 int_divides x + i2)``,
  REWRITE_TAC [eval_form_def, posinf_def]);

val phase5_CONV  = let
  (* have something of the form
       (?x. K (0 < x /\ x <= k) x  /\ eval_form (neginf f) x) \/
       (?b k. (b IN Xset pos f /\ K (0 < k /\ k <= d) k) /\
              eval_form f (b + k))
  *)
  val prelim_left = BINDER_CONV (RAND_CONV (REWRITE_CONV [eval_form_posinf,
                                                          eval_form_neginf]))

  val efBETA_CONV = REWRITE_CONV [eval_form_def]
  val efBETA_CONV = profile "phase5.efBETA" efBETA_CONV
  (* if the term t is a conjunct, apply c to the left conjunct, otherwise
     apply directly to the term *)
  fun lconj_CONV c t = if is_conj t then LAND_CONV c t else c t

  val elim_bterms = profile "phase5.er.elim_bterms" elim_bterms
  val elim_bterms_on_right =
    (* the second disjunct produced by phase4 is of form
          ?b k. (b IN ... /\ K (lo < k /\ k <= hi) k) /\ F(b + k) *)
    (* first try eliminating trivial constraints on k *)
    profile "phase5.er.triv" (
    TRY_CONV (STRIP_QUANT_CONV (LAND_CONV (RAND_CONV quick_cst_elim)) THENC
              (BINDER_CONV Unwind.UNWIND_EXISTS_CONV ORELSEC
               REWRITE_CONV [])) ) THENC
    (* at this stage, k may or may not have been eliminated by the previous
       step, either by becoming false, which will have already turned the
       whole term false, or by becoming unwound.
       In the former, the TRY_CONV will do nothing because the LAND_CONV
       will fail.
       Otherwise, the basic action here is to expand out all of the
       "b" possibilities in the list *)
    TRY_CONV (((SWAP_VARS_CONV THENC BINDER_CONV elim_bterms) ORELSEC
               elim_bterms) THENC
              profile "phase5.er.r_i_g" reduce_if_ground THENC
              profile "phase5.er.p1ex" push_one_exists_over_many_disjs)
in
  profile "phase5.el" (LAND_CONV prelim_left) THENC
  profile "phase5.er" (RAND_CONV elim_bterms_on_right) THENC
  profile "phase5.finish"
 (EVERY_DISJ_CONV (TRY_CONV (profile "phase5.finish.fix" fixup_newvar) THENC
                   profile "phase5.finish.div"
                           (ONCE_DEPTH_CONV check_divides) THENC
                   profile "phase5.finish.simpdisj"
                           (TRY_CONV simplify_constrained_disjunct) THENC
                   TRY_CONV (REWR_CONV EXISTS_SIMP))) (* might pick up ?x. t *)
end

val phase5_CONV = profile "phase5" phase5_CONV

end;
