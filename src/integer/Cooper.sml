structure Cooper :> Cooper =
struct

open HolKernel boolLib integerTheory
     arithmeticTheory intSyntax int_arithTheory intSimps;

open CooperShell CooperSyntax

infix THEN THENC THENL |-> ## ORELSEC
infixr -->

val ERR = mk_HOL_ERR "Cooper";

(* this draws on similar code in Richard Boulton's natural number
   arithmetic decision procedure *)

fun contains_var tm = can (find_term is_var) tm
fun is_linear_mult tm =
  is_mult tm andalso
  not (contains_var (rand tm) andalso contains_var (rand (rator tm)))
fun land tm = rand (rator tm)

fun non_zero tm =
    if is_negated tm then non_zero (rand tm)
    else tm <> zero_tm

(* returns a list of pairs, where the first element of each pair is a non-
   Presburger term that occurs in tm, and where the second is a boolean
   that is true if none of the variables that occur in the term are
   bound by a quantifier. *)
fun non_presburger_subterms0 ctxt tm =
  if
    (is_forall tm orelse is_exists1 tm orelse is_exists tm) andalso
    (type_of (bvar (rand tm)) = int_ty)
  then let
    val abst = rand tm
  in
    non_presburger_subterms0 (Lib.union [bvar abst] ctxt) (body abst)
  end
  else if is_neg tm orelse is_absval tm orelse is_negated tm then
    non_presburger_subterms0 ctxt (rand tm)
  else if (is_cond tm) then let
    val (b, t1, t2) = dest_cond tm
  in
    Lib.U [non_presburger_subterms0 ctxt b, non_presburger_subterms0 ctxt t1,
           non_presburger_subterms0 ctxt t2]
  end
  else if (is_great tm orelse is_geq tm orelse is_eq tm orelse
           is_less tm orelse is_leq tm orelse is_conj tm orelse
           is_disj tm orelse is_imp tm orelse is_plus tm orelse
           is_minus tm orelse is_linear_mult tm) then
    Lib.union (non_presburger_subterms0 ctxt (land tm))
              (non_presburger_subterms0 ctxt (rand tm))
  else if (is_divides tm andalso is_int_literal (land tm)) then
    non_presburger_subterms0 ctxt (rand tm)
  else if ((is_div tm orelse is_mod tm) andalso
           is_int_literal (rand tm) andalso
           non_zero (rand tm)) then
    non_presburger_subterms0 ctxt (land tm)
  else if is_int_literal tm then []
  else if is_var tm andalso type_of tm = int_ty then []
  else if (tm = true_tm orelse tm = false_tm) then []
  else [(tm, not (List.exists (fn v => free_in v tm) ctxt))]

val is_presburger = null o non_presburger_subterms0 []
val non_presburger_subterms = map #1 o non_presburger_subterms0 []

fun decide_fv_presburger tm = let
  fun is_int_const tm = type_of tm = int_ty andalso is_const tm
  val fvs = free_vars tm @ (Lib.mk_set (find_terms is_int_const tm))
  fun dest_atom tm = dest_const tm handle HOL_ERR _ => dest_var tm
  fun gen(bv, t) =
    if is_var bv then mk_forall(bv, t)
    else let
      val gv = genvar int_ty
    in
      mk_forall(gv, subst [bv |-> gv] t)
    end
in
  if null fvs then
    decide_pure_presburger_term tm
  else let
    val newtm = List.foldr gen tm fvs   (* as there are no non-presburger
                                           sub-terms, all these variables
                                           will be of integer type *)
  in
    EQT_INTRO (SPECL fvs (EQT_ELIM (decide_pure_presburger_term newtm)))
  end handle HOL_ERR _ =>
    raise ERR "COOPER_CONV"
      ("Tried to prove generalised goal (generalising "^
       #1 (dest_atom (hd fvs))^"...) but it was false")
end


fun abs_inj inj_n tm = let
  val gv = genvar int_ty
  val tm1 = subst [inj_n |-> gv] tm
in
  GSYM (BETA_CONV (mk_comb(mk_abs(gv,tm1), inj_n)))
end

fun eliminate_nat_quants tm = let
in
  if is_forall tm orelse is_exists tm orelse is_exists1 tm then let
    val (bvar, body) = dest_abs (rand tm)
  in
    if type_of bvar = num_ty then let
      val inj_bvar = mk_comb(int_injection, bvar)
      val rewrite_qaway =
        REWR_CONV (if is_forall tm then INT_NUM_FORALL
        else if is_exists tm then INT_NUM_EXISTS
             else INT_NUM_UEXISTS) THENC
        BINDER_CONV (RAND_CONV BETA_CONV)
    in
      BINDER_CONV (abs_inj inj_bvar) THENC rewrite_qaway THENC
      BINDER_CONV eliminate_nat_quants
    end
    else
      BINDER_CONV eliminate_nat_quants
  end
    else if is_neg tm then (* must test for is_neg before is_imp *)
      RAND_CONV eliminate_nat_quants
    else if (is_conj tm orelse is_disj tm orelse is_eq tm orelse
             is_imp tm) then
      BINOP_CONV eliminate_nat_quants
    else if is_cond tm then
      RATOR_CONV (RATOR_CONV (RAND_CONV eliminate_nat_quants))
    else ALL_CONV
end tm handle HOL_ERR {origin_function = "REWR_CONV", ...} =>
  raise ERR "ARITH_CONV" "Uneliminable natural number term remains"


val dealwith_nats = let
  open arithmeticTheory numSyntax
  val rewrites = [GSYM INT_INJ, GSYM INT_LT, GSYM INT_LE,
                  GREATER_DEF, GREATER_EQ, GSYM INT_ADD,
                  GSYM INT_MUL, INT, INT_NUM_COND, INT_NUM_EVEN,
                  INT_NUM_ODD]
  val p_var = mk_var("p", num)
  val q_var = mk_var("q", num)
  fun elim_div_mod0 t = let
    val divmods =
        HOLset.listItems (find_free_terms (fn t => is_mod t orelse is_div t) t)
    fun elim_t to_elim = let
      val ((num,divisor), thm) = (dest_div to_elim, DIV_P)
          handle HOL_ERR _ => (dest_mod to_elim, MOD_P)
      val div_nzero = EQT_ELIM (REDUCE_CONV (mk_less(zero_tm, divisor)))
      val rwt = MP (Thm.INST [p_var |-> num, q_var |-> divisor] (SPEC_ALL thm))
                   div_nzero
    in
      UNBETA_CONV to_elim THENC REWR_CONV rwt THENC
      STRIP_QUANT_CONV (RAND_CONV (RAND_CONV BETA_CONV))
    end
  in
    EVERY_CONV (map elim_t divmods) t
  end
  fun elim_div_mod t = let
    fun recurse tm = let
    in
      if is_exists tm orelse is_forall tm then BINDER_CONV recurse
      else
        elim_div_mod0 THENC SUB_CONV recurse
    end tm
  in
    recurse t
  end
in
  Sub_and_cond.SUB_AND_COND_ELIM_CONV THENC elim_div_mod THENC
  PURE_REWRITE_CONV rewrites THENC eliminate_nat_quants
end

(* subterms is a list of subterms all of integer type *)
fun decide_nonpbints_presburger subterms tm = let
  fun tactic subtm tm =
    (* return both a new term and a function that will convert a theorem
       of the form <new term> = T into tm = T *)
    if is_comb subtm andalso rator subtm = int_injection then let
      val n = rand subtm
      val thm0 = abs_inj subtm tm (* |- tm = P subtm *)
      val tm0 = rhs (concl thm0)
      val gv = genvar num_ty
      val tm1 = mk_forall(gv, mk_comb (rator tm0, mk_comb(int_injection, gv)))
      val thm1 =  (* |- (!gv. P gv) = !x. 0 <= x ==> P x *)
        (REWR_CONV INT_NUM_FORALL THENC
         BINDER_CONV (RAND_CONV BETA_CONV)) tm1
      fun prove_it thm = let
        val without_true = EQT_ELIM thm (* |- !x. 0 <= x ==> P x *)
        val univ_nat = EQ_MP (SYM thm1) without_true
        val spec_nat = SPEC n univ_nat
      in
        EQT_INTRO (EQ_MP (SYM thm0) spec_nat)
      end
    in
      (rhs (concl thm1), prove_it)
    end
    else let
      val gv = genvar int_ty
    in
      (mk_forall(gv, subst [subtm |-> gv] tm),
       EQT_INTRO o SPEC subtm o EQT_ELIM)
    end
  fun gen_overall_tactic tmlist =
    case tmlist of
      [] => raise Fail "Can't happen in decide_nonpbints_presburger"
    | [t] => tactic t
    | (t::ts) => let
        fun doit base = let
          val (subgoal, vfn) = gen_overall_tactic ts base
          val (finalgoal, vfn') = tactic t subgoal
        in
          (finalgoal, vfn o vfn')
        end
      in
        doit
      end
  val overall_tactic = gen_overall_tactic subterms
  val (goal, vfn) = overall_tactic tm
  val thm = decide_fv_presburger goal
in
  vfn thm handle HOL_ERR _ =>
    raise ERR "ARITH_CONV"
      ("Tried to prove generalised goal (generalising "^
       Parse.term_to_string (hd subterms)^"...) but it was false")
end

fun COOPER_CONV tm = let
  fun stage2 tm =
    case non_presburger_subterms0 [] tm of
      [] => decide_fv_presburger tm
    | non_pbs => let
        fun bad_term (t,b) = not b orelse type_of t <> int_ty
      in
        case List.find bad_term non_pbs of
          NONE => decide_nonpbints_presburger (map #1 non_pbs) tm
        | SOME (t,_) => raise ERR "ARITH_CONV"
            ("Not in the allowed subset; consider "^Parse.term_to_string t)
      end
in
  dealwith_nats THENC stage2
end tm

val COOPER_PROVE = EQT_ELIM o COOPER_CONV
val COOPER_TAC = CONV_TAC COOPER_CONV;

end;
