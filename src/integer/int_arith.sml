open HolKernel basicHol90Lib integerTheory Parse

infix THEN THENC THENL |-> ## ORELSEC
infixr -->

val (Type,Term) = parse_from_grammars integerTheory.integer_grammars;
fun -- q x = Term q
fun == q x = Type q

open arithmeticTheory Psyntax intLib int_arithTheory

fun ERR f msg = HOL_ERR {origin_function = f,
                         message = msg,
                         origin_structure = "int_arith"};

val not_tm = Term.mk_const{Name = "~", Ty = Type.bool --> Type.bool}

local open listTheory in end;

fun mk_abs_CONV var term = let
  val rhs = Rsyntax.mk_abs {Body = term, Bvar = var}
  val newrhs = Rsyntax.mk_comb {Rator = rhs, Rand = var}
in
  GSYM (BETA_CONV newrhs)
end

val elim_le = GSYM INT_NOT_LT
val elim_gt = int_gt
val elim_ge = int_ge

val remove_negated_vars = let
  fun remove_negated tm =
    (* turn ~ var into ~1 * var *)
    if is_negated tm andalso is_var (rand tm) then
      REWR_CONV INT_NEG_MINUS1 tm
    else
      NO_CONV tm
in
  DEPTH_CONV remove_negated
end

fun remove_bare_vars tm =
  if is_conj tm orelse is_disj tm orelse is_less tm orelse is_plus tm orelse
     is_divides tm
  then
    BINOP_CONV remove_bare_vars tm
  else if is_neg tm then RAND_CONV remove_bare_vars tm
  else if is_var tm then REWR_CONV (GSYM INT_MUL_LID) tm
  else ALL_CONV tm

val phase1_CONV = let
  fun flip_muls tm =
    if is_mult tm andalso not (is_var (rand tm)) then let
      val mcands = strip_mult tm
      val (var, rest) = Lib.pluck is_var mcands
    in
      EQT_ELIM (AC_CONV (INT_MUL_ASSOC, INT_MUL_SYM)
                (mk_eq(tm, mk_mult(list_mk_mult rest, var))))
    end handle HOL_ERR {origin_structure = "Lib", ...} => ALL_CONV tm
    else if is_comb tm then
      (RATOR_CONV flip_muls THENC RAND_CONV flip_muls) tm
    else
      ALL_CONV tm

in
  (* to push negations inwards; formula must be quantifier free *)
  REDUCE_CONV THENC
  REWRITE_CONV [boolTheory.DE_MORGAN_THM, boolTheory.NOT_IMP, not_less,
                boolTheory.IMP_DISJ_THM, elim_eq, elim_le, elim_ge, elim_gt,
                INT_SUB_CALCULATE, INT_RDISTRIB, INT_LDISTRIB,
                INT_NEG_LMUL] THENC
  remove_negated_vars THENC remove_bare_vars THENC flip_muls THENC REDUCE_CONV
end

fun sum_var_coeffs var tm = let
  open Arbint
in
  if is_plus tm then
    sum_var_coeffs var (rand (rator tm)) + sum_var_coeffs var (rand tm)
  else if is_mult tm then let
    val (l,r) = (rand (rator tm), rand tm)
  in
    if r = var then int_of_term l else zero
  end else zero
end

datatype dir = Left | Right

fun term_at Left tm = rand (rator tm)
  | term_at Right tm = rand tm

fun conv_at Left = RATOR_CONV o RAND_CONV
  | conv_at Right = RAND_CONV

(* moves summands from one side or the other of a less-than term *)
fun move_terms_from dir P tm = let
  val arg = term_at dir tm
  val arg_summands = strip_plus arg
in
  case partition P arg_summands of
    ([], to_stay) => REFL tm  (* none to move *)
  | (to_move, []) => let
      (* all must move *)
      val move_conv =
        case dir of
          Left => REWR_CONV move_all_right
        | Right => REWR_CONV move_all_left
    in
      (move_conv THENC REWRITE_CONV [INT_NEG_ADD, INT_NEGNEG,
                                     INT_NEG_LMUL]) tm
    end
  | (to_move, to_stay) => let
      val new_arg = mk_plus(list_mk_plus to_move, list_mk_plus to_stay)
      val arg_eq_new = EQT_ELIM (AC_CONV (INT_ADD_ASSOC, INT_ADD_COMM)
                                         (mk_eq(arg, new_arg)))
      val move_conv =
        case dir of
          Left => REWR_CONV move_left_right
        | Right => REWR_CONV move_left_left
    in
      (conv_at dir (K arg_eq_new) THENC move_conv THENC
       REWRITE_CONV [INT_NEG_ADD, INT_NEGNEG, INT_NEG_LMUL]) tm
    end
end

fun collect_terms tm = let
  (* assuming that tm is of the form c * x + d * x + e * x
     turns it into (c + d + e) * x
  *)
in
  if is_plus tm then
    BINOP_CONV collect_terms THENC REWR_CONV (GSYM INT_RDISTRIB)
  else
    ALL_CONV
end tm

fun collect_in_sum var tm = let
  (* all terms involving var in tm are collected together such that the
     form of the tm becomes c * var + e *)
  val summands = strip_plus tm
in
  case partition (free_in var) summands of
    ([], _) => ALL_CONV tm
  | (_, []) => collect_terms tm
  | (withvar, without) => let
      val newterm = mk_plus(list_mk_plus withvar, list_mk_plus without)
      val tm_eq_newterm = EQT_ELIM (AC_CONV (INT_ADD_ASSOC, INT_ADD_COMM)
                                    (mk_eq(tm, newterm)))
    in
      (K tm_eq_newterm THENC (RATOR_CONV (RAND_CONV collect_terms))) tm
    end
end


(* phase 2 massages the terms so that all of the < terms have one side or
   the other with just n * x on it, where n is a non-negative integer, and x
   is the variable we're going to eliminate, unless x can be entirely
   eliminated, in which case the 0 * x is reduced to 0.

   Further, all of the int_divides terms (negated or not) involving
   our variable are cast in the form
     c1 int_divides (c2 * x) + e
   where both c1 and c2 are positive constants
*)
val INT_DIVIDES_NEG = CONV_RULE (DEPTH_CONV FORALL_AND_CONV) INT_DIVIDES_NEG
fun phase2_CONV var tm = let
  val land = rand o rator
  fun dealwith_negative_divides tm = let
    val coeff = if is_plus (rand tm) then land (land (rand tm))
                else land (rand tm)
  in
    if is_negated coeff then
      REWR_CONV (GSYM (CONJUNCT1 INT_DIVIDES_NEG)) THENC
      REWRITE_CONV [INT_NEG_ADD, INT_NEG_LMUL, INT_NEGNEG]
    else
      ALL_CONV
  end tm
  fun collect_up_other_freevars tm = let
    val fvs = free_vars tm
  in
    EVERY_CONV (map collect_in_sum fvs) tm
  end
in
  if is_disj tm orelse is_conj tm then
    BINOP_CONV (phase2_CONV var) tm
  else if is_less tm then let
    open Arbint
    val var_onL = sum_var_coeffs var (rand (rator tm))
    val var_onR = sum_var_coeffs var (rand tm)
    val (dir1, dir2) = if var_onL < var_onR then (Left, Right)
                       else (Right, Left)
    val move_CONV =
      move_terms_from dir1 (free_in var) THENC
      move_terms_from dir2 (not o free_in var)
  in
    (move_CONV THENC conv_at dir2 collect_terms THENC
     conv_at dir1 collect_up_other_freevars THENC
     TRY_CONV (conv_at dir1 collect_additive_consts) THENC
     simpLib.SIMP_CONV int_ss [INT_MUL_LZERO, INT_ADD_LID, INT_ADD_RID]) tm
  end else if is_neg tm then RAND_CONV (phase2_CONV var) tm
  else if is_divides tm then
    (TRY_CONV (REWR_CONV (CONJUNCT2 INT_DIVIDES_NEG)) THENC
     RAND_CONV (collect_in_sum var) THENC REDUCE_CONV THENC
     dealwith_negative_divides THENC
     REWRITE_CONV [INT_MUL_LZERO] THENC REDUCE_CONV) tm
  else ALL_CONV tm
end

(* phase three takes all of the coefficients of the variable we're
   eliminating, and calculates their LCM.  Every term is then altered to
   be of the form
        LCM x < ..   or  .. < LCM x
   Then, we can rewrite
     ?x.  .... LCM x ... LCM x ...
   to
     ?x'. .... x' .... x' .... /\ LCM divides x'
   every occurrence of LCM x is replaced with a new variable

*)

fun find_coeff_less var term = let
  val (_, args) = strip_comb term  (* operator will be < *)
  val arg1 = hd args
  val arg2 = hd (tl args)
in
  if is_mult arg1 andalso rand arg1 = var then
    SOME (int_of_term (rand (rator arg1)))
  else if is_mult arg2 andalso rand arg2 = var then
    SOME (int_of_term (rand (rator arg2)))
  else
    NONE
end

fun find_coeff_divides var term = let
  val (_, args) = strip_comb term (* operator will be int_divides *)
  val arg = hd (tl args)  (* first arg is uninteresting, it should be
                             just a constant *)
  fun recurse_on_rhs t =
    if is_plus t then recurse_on_rhs (rand (rator t))
    else if is_mult t andalso rand t = var then
      SOME (int_of_term (rand (rator t)))
    else
      NONE
in
  recurse_on_rhs arg
end

fun find_coeffs var term = let
  (* have term of the form
       c * x < e <op> e < c * x <op> ...
     want to get list of c's, which should all be integer constants.
     It's possible that some terms will have been 0 * x and then simplified
     to just 0 < e or e < 0.  These can be ignored.
  *)
  fun deal_with_less acc tm =
    case find_coeff_less var tm of
      NONE => acc
    | SOME i => i :: acc
  fun recurse acc tm =
    if is_disj tm orelse is_conj tm then
      recurse (recurse acc (rand tm)) (rand (rator tm))
    else if is_less tm then
      deal_with_less acc tm
    else if is_neg tm then (* arises only over int_divides *)
      recurse acc (rand tm)
    else if is_divides tm then
      case find_coeff_divides var tm of
        NONE => acc
      | SOME x => x :: acc
    else
      acc
in
  Lib.mk_set (recurse [] term)
end

fun find_coeff var term =
  if is_divides term then find_coeff_divides var term
  else if is_less term then find_coeff_less var term
  else if is_neg term then find_coeff var (rand term)
  else NONE

(*---------------------------------------------------------------------------*)
(* Function to compute the Greatest Common Divisor of two integers.          *)
(*---------------------------------------------------------------------------*)

fun gcd (i,j) = let
  exception non_neg
  open Arbint
  fun gcd' (i,j) = let
    val r = (i mod j)
  in
    if (r = zero) then j else gcd' (j,r)
  end
in
  (if ((i < zero) orelse (j < zero)) then raise non_neg
  else if (i < j) then gcd' (j,i) else gcd' (i,j))
  handle _ => raise ERR "gcd" "negative arguments to gcd"
end;

(*---------------------------------------------------------------------------*)
(* Function to compute the Lowest Common Multiple of two integers.           *)
(*---------------------------------------------------------------------------*)

fun lcm (i,j) = let open Arbint in (i * j) div (gcd (i,j)) end
handle _ => raise ERR "lcm" "negative arguments to lcm";

fun calc_lcm ints =
  case ints of
    [] => raise Fail "Should never happen"
  | [x] => x
  | (x::y::xs) => calc_lcm (lcm (x, y)::xs)



(* this phase has to be done at the level of the existential quantifier *)
(* assume that the existential quantifier still has occurrences of the
   bound variable in the body *)
fun phase3_CONV term = let
  val (var, body) = Psyntax.dest_exists term
  (* first calculate the desired LCM *)
  val coeffs = find_coeffs var body
  val lcm = calc_lcm coeffs
  (* now descend to each less-than term, and update the coefficients of
     var to be the same lcm *)
  fun multiply_by_CONV i tm = let
    val zero_lti = EQT_ELIM (REDUCE_CONV (mk_less(zero_tm, term_of_int i)))
    val divides_conv =
      REWR_CONV (MATCH_MP justify_divides zero_lti) THENC
      RAND_CONV (TRY_CONV (REWR_CONV INT_LDISTRIB)) THENC REDUCE_CONV
  in
    if is_divides tm then divides_conv
    else if is_neg tm then RAND_CONV divides_conv
    else REWR_CONV (MATCH_MP justify_multiplication zero_lti)
  end tm

  fun LCMify term =
    if is_disj term orelse is_conj term then
      BINOP_CONV LCMify term
    else
      case (find_coeff var term) of
        NONE => ALL_CONV term
      | SOME c => multiply_by_CONV (Arbint.div(lcm, c)) term

  fun absify_CONV tm = let
    val arg = mk_mult(term_of_int lcm, var)
    val body = Term.subst[(arg |-> var)] tm
  in
    SYM (BETA_CONV (mk_comb(mk_abs(var, body), arg)))
  end

in
  (BINDER_CONV (LCMify THENC
                REWRITE_CONV [INT_LDISTRIB, INT_RDISTRIB, INT_MUL_ASSOC] THENC
                REDUCE_CONV THENC absify_CONV) THENC
   REWR_CONV lcm_eliminate THENC
   RENAME_VARS_CONV [#Name (Term.dest_var var)] THENC
   BINDER_CONV (RATOR_CONV (RAND_CONV BETA_CONV)) THENC
   DEPTH_CONV collect_additive_consts)
  term
end

fun resquan_remove tm =
  (REWR_CONV restricted_quantification_simp THENC
   REDUCE_CONV THENC REWRITE_CONV [] THENC
   TRY_CONV (RAND_CONV resquan_remove) THENC REWRITE_CONV []) tm

(* Phase 4 *)

val simple_bool_formula =
  tautLib.TAUT_PROVE (Term`!p q. ~(p /\ q) = (p ==> ~q)`)

fun prove_membership t1 t2 = let
  val (tmlist, elty) = dest_list t2
  fun recurse preds thmtodate laters =
    case (thmtodate, preds, laters) of
      (NONE, _, []) => raise ERR "prove_membership" "term not found in list"
    | (NONE, _, x::xs) =>
        if x = t1 then let
          val tailtm = mk_list(xs, elty)
          val whole_list = mk_cons(x, tailtm)
        in
          recurse preds (SOME (ISPECL [x, tailtm] MEM_base, whole_list)) []
        end
        else
          recurse (x::preds) NONE xs
    | (SOME (thm,_), [], _) => thm
    | (SOME (thm,tmlist), p::ps, _) => let
        val newlist = mk_cons(p, tmlist)
        val newthm = MP (ISPECL [tmlist, t1, p] MEM_build) thm
      in
        recurse ps (SOME (newthm, newlist)) []
      end
in
  recurse [] NONE tmlist
end

fun phase4_CONV tm = let
  (* have a formula of the form
       ?x. t1 <op> t2 <op> t3 <op> .... <tn>
     where each <op> is either /\ or \/ and
     where each ti either doesn't involve x at all, or is one of the
     following forms:
        x < a,
        b < x,
        d int_divides x + u
        ~(e int_divides x + v)
     and where all of a, b, u and v are expressions not involving x.
     Further there will be at least one of the latter two.

     Want to calculate F_neginf such that each term of the first type is
     replaced by TRUE and each of the second replaced by FALSE.
  *)
  val {Bvar, Body} = Rsyntax.dest_exists tm
  val F = rand tm
  val Fx = mk_comb(F, Bvar)
  (* need prove that ?y. !x. x < y ==> (neginf x = F x) *)
  val lemma = let
    val lt_terms = let
      (* collect up all of the terms that appear on either side of a < with
         x on the other side *)
      fun recurse acc tm =
        if is_disj tm orelse is_conj tm then
          recurse (recurse acc (rand tm)) (rand (rator tm))
        else if is_less tm then
          if rand tm = Bvar then rand (rator tm)::acc
          else if rand (rator tm) = Bvar then rand tm :: acc
          else acc
        else acc
    in
      Lib.mk_set (recurse [] Body)
    end
    val y = genvar int_ty
  in
    if null lt_terms then let
      (* neginf and F are the same *)
      val without_ex = GEN Bvar (DISCH (mk_less(Bvar, y)) (REFL Fx))
    in
      EXISTS (mk_exists(y, concl without_ex), y) without_ex
    end
    else let
      val witness = let
        infixr -->
        fun recurse acc tms =
          case tms of
            [] => acc
          | (x::xs) => recurse (list_mk_comb(min_tm, [acc, x])) xs
      in
        recurse (hd lt_terms) (tl lt_terms)
      end
      fun gen_rewrites acc thm =
        if is_conj (concl thm) then
          gen_rewrites (gen_rewrites acc (CONJUNCT1 thm)) (CONJUNCT2 thm)
        else let
          val rhs = rand (concl thm)
          val (hd, _) = strip_comb rhs
        in
          if hd = min_tm then
            gen_rewrites acc (MATCH_MP INT_MIN_LT thm)
          else
            EQT_INTRO thm::(EQF_INTRO (MATCH_MP INT_LT_GT thm))::acc
        end
      val rewrites = gen_rewrites [] (ASSUME (mk_less (Bvar, witness)))
      val thm0 =
        (BETA_CONV THENC REWRITE_CONV rewrites THENC mk_abs_CONV Bvar) Fx
      val thm1 = GEN Bvar (DISCH_ALL thm0)
      val exform = let
        val (x, body) = dest_forall (concl thm1)
        val (_,c) = dest_imp body
        val newh = mk_less(x, y)
      in
        mk_exists(y, mk_forall(x, mk_imp(newh, c)))
      end
    in
      EXISTS (exform, witness) thm1
    end
  end
  val neginf =
    rator (rhs (#2 (dest_imp (#2 (dest_forall
                                  (#2 (dest_exists (concl lemma))))))))

  (* before proceeding, need to calculate the LCM of all the d and e of
     the above forms, call it delta *)

  val all_delta_tms = let
    fun recurse acc tm =
      if is_disj tm orelse is_conj tm then
        recurse (recurse acc (rand tm)) (rand (rator tm))
      else if is_neg tm then recurse acc (rand tm)
      else if is_divides tm then let
        val x_on_rhs =
          (is_plus (rand tm) andalso (rand (rator (rand tm)) = Bvar)) orelse
          (rand tm = Bvar)
      in
        if x_on_rhs then rand (rator tm) :: acc
        else acc
      end
      else
        acc
  in
    Lib.mk_set (recurse [] Body)
  end
  val all_deltas = map int_of_term all_delta_tms
  val delta = calc_lcm all_deltas
  val delta_tm = term_of_int delta
  val divides_info =
    map (fn ld_tm =>
         (ld_tm, EQT_ELIM (REDUCE_CONV (mk_divides(ld_tm, delta_tm)))))
    all_delta_tms
  (* further need that !x y. neginf x = neginf (x - y * delta_tm) *)

  (* The argument to neginf only appears as argument to divides terms.
     We must be able to reduce
       c int_divides (x - y * delta + e)   to
       c int_divides (x + e)
     given that c is a divisor of delta.  We first reduce
       (x - y + e) to (x + e - y)  using theorem move_sub (proved above)
     then we have
       c int_divides y ==> (c int_divides (x - y) = c int_divides x)  and
       c int_divides x ==> c int_divides (x * y)
     which we specialise with the appropriate values for x and y, and then
     use rewriting to do the right reductions
  *)
  val lemma2 = let
    val y = genvar int_ty
    val tm0 = mk_comb (neginf,
                       list_mk_comb(minus_tm, [Bvar, mk_mult(y, delta_tm)]))
    fun recurse tm =
      if is_conj tm orelse is_disj tm then
        BINOP_CONV recurse tm
      else if is_neg tm then
        RAND_CONV recurse tm
      else if
        is_divides tm andalso #1 (strip_comb (rand tm)) = minus_tm
      then let
        val local_delta = rand(rator tm)
        val ldel_divides = Lib.assoc local_delta divides_info
        val ldel_divides_dely =
          SPEC y (MATCH_MP INT_DIVIDES_RMUL ldel_divides)
        val ldel_simpler = MATCH_MP INT_DIVIDES_RSUB ldel_divides_dely
      in
        REWR_CONV ldel_simpler tm
      end
      else ALL_CONV tm

    val c =
      BETA_CONV THENC REWRITE_CONV [move_sub] THENC recurse THENC
      mk_abs_CONV Bvar
  in
    GENL [y, Bvar] (c tm0)
  end

  val disj1 = let
    val i = genvar int_ty
    val restriction = mk_conj(mk_less(zero_tm, i),
                              mk_lesseq(i, delta_tm))
  in
    mk_exists(i, mk_conj(restriction, mk_comb(neginf, i)))
  end

  val (disj2, bis_list_tm) = let
    (* need all of the bi *)
    val intlist_ty = Type.mk_type{Args = [int_ty], Tyop = "list"};
    val MEM_tm = Term.mk_const{Name = "MEM",
                               Ty = int_ty --> intlist_ty --> Type.bool}
    fun find_bis acc tm =
      if is_disj tm orelse is_conj tm then
        find_bis (find_bis acc (rand tm)) (rand (rator tm))
      else if is_less tm andalso rand tm = Bvar then
        rand (rator tm) :: acc
      else
        acc
    val bis = find_bis [] Body
    val bis_list_tm = mk_list(bis, int_ty)
    val b = genvar int_ty
    val j = genvar int_ty
    val brestriction = list_mk_comb(MEM_tm, [b, bis_list_tm])
    val jrestriction = mk_conj(mk_less(zero_tm, j), mk_lesseq(j, delta_tm))
  in
    (list_mk_exists([b,j], mk_conj(mk_conj(brestriction, jrestriction),
                                   mk_comb(F, mk_plus(b,j)))),
     bis_list_tm)
  end

  (* now must prove that (?x. F x) = disj1 \/ disj2 *)
  (* first show disj1 ==> (?x. F x) *)

  (* we have
       lemma:         ?y. !x. x < y ==> (F(x) = neginf(x))
       choose y:      !x. x < y ==> F(x) = neginf(x)                 (1)
       assumption:    ?c. (0 < c /\ c <= delta) /\ neginf(c)
       lemma2:        !x y. neginf(x - y * delta) = neginf(x)
       can_get_small: !x y d. 0 < d ==> ?c. 0 < c /\ y - c * d < x

     need a z such that z < y and neginf(z).  Then F(z) will be true.
     Specialise can_get_small with
           y, c and delta
     so
                      0 < delta ==> ?e. 0 < e /\ c - e * delta < y
     discharge 0 < delta to get
                      ?e. 0 < e /\ c - e * delta < y
     choose e, take second conjunct
                      c - e * delta < y                              (2)
     specialise lemma2 with c, e
                      neginf(c - e * delta) = neginf(c)              (3)
     MATCH_MP (1) and (2)
                      F(c - e * delta) = neginf(c - e * delta)       (4)
     trans with (3) to get
                      F(c - e * delta) = neginf(c)                   (5)
     given assumption,
                      F(c - e * delta)                               (6)
     so, there exists an x, such that F is true
                      ?x. F x                                        (7)

  *)
  val zero_lt_delta = EQT_ELIM (REDUCE_CONV (mk_less(zero_tm, delta_tm)))
  val disj1_implies_exFx = let
    val (disj1_var, disj1_body) = dest_exists disj1
    val assumption0 = ASSUME disj1_body
    val assumption = CONJUNCT2 assumption0
    val lemma_var = genvar int_ty
    val thm1 = let
      val (exvar, lemma_body) = dest_exists (concl lemma)
    in
      ASSUME (Term.subst [exvar |-> lemma_var] lemma_body)
    end
    val c = rand (concl assumption)
    val spec_cgs = SPECL [lemma_var, c, delta_tm] can_get_small
    val thm0 = MP spec_cgs zero_lt_delta
    val e = genvar int_ty
    val thm2 = let
      val (v, body) = dest_exists (concl thm0)
    in
      CONJUNCT2 (ASSUME (Term.subst [v |-> e] body))
    end
    val thm3 = SPECL [e,c] lemma2
    val thm4 = MATCH_MP thm1 thm2
    val thm5 = TRANS thm4 thm3
    val thm6 = EQ_MP (SYM thm5) assumption
    val thm7 = EXISTS (tm, rand (concl thm6)) (CONV_RULE BETA_CONV thm6)
  in
    CHOOSE(disj1_var, ASSUME disj1)
    (CHOOSE (lemma_var, lemma)
     (CHOOSE(e, thm0) thm7))
  end

  (* now need to prove that disj2 implies ?x. F x -- this is much
     simpler, because each disjunct of disj2 is just about an instance
     of F c *)

  val disj2_implies_exFx = let
    val (disj2_vars, disj2_body) = strip_exists disj2
    val assumption0 = ASSUME disj2_body
    val assumption = CONJUNCT2 assumption0
    val thm0 =
      EXISTS(tm, rand(concl assumption)) (CONV_RULE BETA_CONV assumption)
    val (b,j) = (hd disj2_vars, hd (tl disj2_vars))
  in
    CHOOSE(b, ASSUME disj2)
    (CHOOSE (j, ASSUME (mk_exists(j, disj2_body))) thm0)
  end
  val rhs_implies_exFx =
    DISCH_ALL (DISJ_CASES (ASSUME(mk_disj(disj1, disj2)))
               disj1_implies_exFx disj2_implies_exFx)

  (* to do the proof of exFx implies rhs, reason as follows:
       F x0                    (choose_x)
     specialise excluded middle to get
       disj2 \/ ~disj2         (disj2_exm)
     then
       disj2 |- disj2
     allows
       disj2 |- disj1 \/ disj2 (positive_disj2)

     with the other case, (not_disj2) we want to prove that
       !x. F x ==> F (x - delta)

     first rewrite not_disj2 with NOT_EXISTS_CONV twice and then
     tautLib.TAUT_PROVE ``~(p /\ q) = p ==> ~q``.  This will generate
     not_thm:
        |- !b j. MEM b [b1; b2; .. bn] /\ 0 < j /\ j <= delta ==>
                 ~F(b + j)

     so, ASSUME
       F x |- F x          (fx_thm)

     expand out F(x - delta) (i.e. do a BETA_CONV) and traverse this
     and F(x) in parallel.  This is a recursive procedure that takes
     a F(x) theorem and a F(x - delta) term and produces a theorem
     with the second term as its conclusion

     Recursive cases are as follows:
        if is_conj thm then
           CONJ (recurse (CONJUNCT1 thm) (#1 (dest_conj tm)))
                (recurse (CONJUNCT2 thm) (#2 (dest_conj tm)))
        else if is_disj thm then let
           val (d1_thm0, d2_thm0) = (ASSUME ## ASSUME) (dest_disj (concl thm))
           val (d1_tm, d2_tm) = dest_disj tm
           val d1_thm = recurse d1_thm0 d1_tm
           val d2_thm = recurse d2_thm0 d2_tm
        in
           DISJ_CASES thm d1_thm d2_thm
        end

    There are four base cases depending on the form of the term

         (A)   thm = |- x < e
              tm  =    x - d < e

              0 < d              (zero_lt_delta)
           specialise INT_LT_ADD2 with x, e, 0, d to get
              x < e /\ 0 < d ==> x + 0 < e + d
           discharge with conjunction of thm and zero_lt_delta to get
              x + 0 < e + d
           CONV_RULE (RATOR_CONV (RAND_CONV (REWR_CONV INT_ADD_RID))) to get
              x < e + d
           CONV_RULE (REWR_CONV (GSYM INT_LT_SUB_ADD)) to get
              x - d < e
           as required

         (B)   thm = |- e < x
              tm  =    e < x - d

             ASSUME ~tm
                 ... |- ~(e < x - d)                 (not_tm)
             REWR_CONV with INT_NOT_LT
                     |- x - d <= e
             REWR_CONV with INT_LE_SUB_RADD
                     |- x <= e + d                   (var_leq)
             REWR_CONV (thm /\ var_leq) with in_additive_range
                     |- ?j. (x = e + j) /\ 0 < j /\ j <= d  (exists_j)

             demonstrate that e is in the list of bis,
                     |- MEM e [b1; b2; ... bn]       (membership)
             choose j from exists_j and take conjunct1
                     |- x = e + j                    (var_eq)
             and conjunct2
                     |- 0 < j /\ j <= d              (j_in_range)
             match not_thm with membership /\ j_in_range
                     |- ~F(e + j)
             EQF_INTRO
                     |- F(e + j) = F                 (not_fej)
             AP_TERM F (var_eq)
                     |- F(x) = F(e + j)              (fx_eq_fej)
             TRANS fx_eq_fej not_fej
                     |- F(x) = F                     (fx_eq_F)
             EQ_MP fx_thm fx_eq_F
                     |- F
             CCONTR tm
                     |- e < x - d      as required

         (C)  and (D)

              thm = |- f int_divides (x + e)
              tm  =    f int_divides (x - d + e)

             or negated versions of both

             specialise INT_DIVIDES_RMUL and match with divides_info
             theorem that f int_divides d to get
                  f int_divides (c * d)
             specialise INT_DIVIDES_RSUB to get
                  f int_divides (c * d) ==>
                  (f int_divides (x + e) - (c * d) = f int_divides (x + e))
             match two preceding and GSYM to get
                  f int_divides (x + e) = f int_divides (x + e) - c * d
             and if C) then EQ_MP this thm to get result.
             else if D) EQ_MP (AP_TERM ``~`` this) thm to get result

        *)

  val exFx_implies_rhs = let
    val disj2_exm = SPEC disj2 EXCLUDED_MIDDLE
    val positive_disj2 = DISJ2 disj1 (ASSUME disj2)
    val fx_goes_downward = let
      (* to prove ~disj2 |- !x. F x ==> F (x - d) *)
      val not_disj2_0 = mk_neg disj2
      val not_disj2_thm = ASSUME not_disj2_0
      val not_thm =
        CONV_RULE (NOT_EXISTS_CONV THENC
                   BINDER_CONV NOT_EXISTS_CONV THENC
                   STRIP_QUANT_CONV (REWR_CONV simple_bool_formula))
        not_disj2_thm
      val fx_thm = ASSUME (mk_comb(F, Bvar))
      val fx_thm_expanded = CONV_RULE BETA_CONV fx_thm
      val fxd_beta_thm = BETA_CONV (mk_comb(F, mk_minus(Bvar, delta_tm)))
      val fxd_tm = rhs (concl fxd_beta_thm)
      fun recurse thm tm =
        if is_conj tm then let
          val (c1, c2) = dest_conj tm
        in
          CONJ (recurse (CONJUNCT1 thm) c1) (recurse (CONJUNCT2 thm) c2)
        end
        else if is_disj tm then let
          val (d1_thm0, d2_thm0) = (ASSUME ## ASSUME) (dest_disj (concl thm))
          val (d1_tm, d2_tm) = dest_disj tm
          val d1_thm = DISJ1 (recurse d1_thm0 d1_tm) d2_tm
          val d2_thm = DISJ2 d1_tm (recurse d2_thm0 d2_tm)
        in
          DISJ_CASES thm d1_thm d2_thm
        end
        (* base cases *)
        else if is_less tm andalso rand (rator (concl thm)) = Bvar then let
          (* x < e *)
          val e = rand (concl thm)
          val thm0 = SPECL [Bvar, e, zero_tm, delta_tm] INT_LT_ADD2
          val thm1 = MP thm0 (CONJ thm zero_lt_delta)
          val thm2 =
            CONV_RULE (RATOR_CONV (RAND_CONV (REWR_CONV INT_ADD_RID))) thm1
        in
          CONV_RULE (REWR_CONV (GSYM INT_LT_SUB_RADD)) thm2
        end
        else if is_less tm andalso rand (concl thm) = Bvar then let
          (* e < x *)
          val e = rand (rator tm)
          val not_tm = ASSUME (mk_neg tm)
          val var_leq = CONV_RULE (REWR_CONV INT_NOT_LT THENC
                                   REWR_CONV INT_LE_SUB_RADD) not_tm
          val exists_j =
            CONV_RULE (REWR_CONV in_additive_range) (CONJ thm var_leq)
          val membership = prove_membership e bis_list_tm
          (* choose j from exists_j *)
          val (jvar, jbody) = dest_exists (concl exists_j)
          val choose_j = ASSUME jbody
          val var_eq = CONJUNCT1 choose_j
          val j_in_range = CONJUNCT2 choose_j
          val not_fej =
            EQF_INTRO (MATCH_MP not_thm (CONJ membership j_in_range))
          val fx_eq_fej = AP_TERM F var_eq
          val fx_eq_F = TRANS fx_eq_fej not_fej
          val contradiction = EQ_MP fx_eq_F fx_thm
        in
          CCONTR tm (CHOOSE(jvar, exists_j) contradiction)
        end
        else let
          fun is_vardivides tm =
            is_divides tm andalso (rand tm = Bvar orelse
                                   is_plus (rand tm) andalso
                                   rand (rator (rand tm)) = Bvar)
          val thmconcl = concl thm
        in
          if
            is_vardivides thmconcl orelse
            (is_neg thmconcl andalso is_vardivides (rand thmconcl))
          then let
            (* have f int_divides e in thm, possibly under negation *)
            val (f, e, munger) =
              if is_neg thmconcl then (rand (rator (rand thmconcl)),
                                       rand (rand thmconcl),
                                       AP_TERM not_tm)
              else (rand (rator thmconcl), rand thmconcl, (fn x => x))
            val f_div_d = Lib.assoc f divides_info
            val thm0 = MP (SPECL [f, delta_tm, e] INT_DIVIDES_RSUB) f_div_d
            val thm1 =
              if is_plus e then
                CONV_RULE (RATOR_CONV   (* $= (f int_divides x - 6 + y) *)
                           (RAND_CONV   (* f int_divides x - 6 + y *)
                            (RAND_CONV  (* x - 6 + y *)
                             (REWR_CONV (GSYM move_sub))))) thm0
              else
                thm0
            val thm2 = SYM thm1
              (* f int_divides x = f int_divides (x - d) *)
            val thm3 = munger thm2
          in
            EQ_MP thm3 thm
          end
          else
            thm
        end
      val fxd_thm = recurse fx_thm_expanded fxd_tm
    in
      GEN Bvar (DISCH Fx (EQ_MP (SYM fxd_beta_thm) fxd_thm))
    end
    val x0 = genvar int_ty
    val Fx0 = mk_comb(F, x0)
    val Fx0_thm = ASSUME Fx0
    val can_reduce_by_dmultiples =
      MP (SPECL [F, delta_tm, x0] top_and_lessers)
         (CONJ fx_goes_downward Fx0_thm)
    (* this looks like: .. |- !c. 0 < c ==> F (x0 - c * d) *)
    (* further have lemma:
                           |- ?y. !x. x < y ==> (F x = neginf x)
       and lemma2:         |- !c x. neginf (x - c * d) = neginf x
       and can_get_small:  |- !x y d. 0 < d ==> ?c. 0 < c /\ y - c * d < x

       so, choose a y for lemma
          (choose_lemma) . |- !x. x < y ==> (F x = neginf x)
    *)
    val y = genvar int_ty
    val choose_lemma = let
      val (exvar, exbody) = dest_exists (concl lemma)
    in
      ASSUME (Term.subst [exvar |-> y] exbody)
    end
    (*
       specialise can_get_small with [y, x0, d] and MP with zero_lt_delta
          (little_c_ex)    |- ?c. 0 < c /\ x0 - c * d < y
    *)
    val little_c_ex = MP (SPECL [y, x0, delta_tm] can_get_small) zero_lt_delta
    (*
       choose a u for little c
          (choose_u)     . |- 0 < u /\ x0 - u * d < y
       conjunct1
          (zero_lt_u)    . |- 0 < u
       conjunct2
          (x0_less_ud)   . |- x0 - u * d < y
     *)
    val u = genvar int_ty
    val choose_u = let
      val (exvar, exbody) = dest_exists (concl little_c_ex)
    in
      ASSUME (Term.subst [exvar |-> u] exbody)
    end
    val zero_lt_u = CONJUNCT1 choose_u
    val x0_less_ud = CONJUNCT2 choose_u
    (*
       SPEC can_reduce_by_dmultiples with u, and MP with zero_lt_u to get
          (Fx0_less_ud)   . |- F (x0 - u * d)
    *)
    val Fx0_less_ud = MP (SPEC u can_reduce_by_dmultiples) zero_lt_u
    (* SPEC choose_lemma with x0 - u * d and MP with x0_less_ud to get
     (Fneginf_x0_less_ud) . |- F (x0 - u * d) = neginf (x0 - u * d)
    *)
    val x0_less_ud_tm = rand (rator (concl x0_less_ud))
    val Fneginf_x0_less_ud =
      MP (SPEC x0_less_ud_tm choose_lemma) x0_less_ud
    (* EQ_MP with Fx0_less_ud to get
      (neginf_x0_less_ud) . |- neginf (x0 - u * d)
    *)
    val neginf_x0_less_ud = EQ_MP Fneginf_x0_less_ud Fx0_less_ud
    (* have subtract_to_small
                            |- !x d. 0 < d ==>
                                     ?k. 0 < x - k * d /\ x - k * d <= d
       so specialise this with x0 - u * d and delta_tm, and then MP with
       zero_lt_delta to get
         (exists_small_k)   |- ?k. 0 < x0 - u * d - k * d   /\
                                   x0 - u * d - k * d <= d
    *)
    val exists_small_k =
      MP (SPECL [x0_less_ud_tm, delta_tm] subtract_to_small) zero_lt_delta
    (*
       choose k, to get
         (choose_k)         |- 0 < x0 - u * d - k * d /\ x0 - u*d - k*d <= d
    *)
    val k = genvar int_ty
    val choose_k = let
      val (exvar, exbody) = dest_exists (concl exists_small_k)
    in
      ASSUME (Term.subst [exvar |-> k] exbody)
    end
    val u0_less_crap = rand (rand (rator (concl choose_k)))
    val neginf_crap_eq = SPECL [k, x0_less_ud_tm] lemma2
    val neginfo_crap = EQ_MP (SYM neginf_crap_eq) neginf_x0_less_ud
    val disj1_body = CONJ choose_k neginfo_crap
    val disj1_exists = EXISTS(disj1, u0_less_crap) disj1_body
    val disj1_or_disj2 = DISJ1 disj1_exists disj2
    (* now start discharging the choose obligations *)
    val res0 = CHOOSE (k, exists_small_k) disj1_or_disj2
    val res1 = CHOOSE (u, little_c_ex) res0
    val res2 = CHOOSE (y, lemma) res1
    (* and do disj_cases on excluded_middle *)
    val res3 = DISJ_CASES disj2_exm positive_disj2 res2
    (* choose on x0 to get an existential assumption *)
    val res4 = CHOOSE (x0, ASSUME (mk_exists(Bvar, Fx))) res3
  in
    CONV_RULE (RATOR_CONV (RAND_CONV (BINDER_CONV BETA_CONV)))
              (DISCH_ALL res4)
  end
in
  IMP_ANTISYM_RULE exFx_implies_rhs rhs_implies_exFx
end

val simple_bool_2 = tautLib.TAUT_PROVE (Term`!p. T \/ p = T`)
val simple_bool_3 = tautLib.TAUT_PROVE (Term`!p. F \/ p = p`)
val phase5_CONV = let
  (* have something of the form
       (?x. 0 < x /\ x <= k /\ neginf x) \/
       (?b k. MEM b [..] /\ 0 < k /\ k <= d /\ F (b + k))
  *)
  val LAND_CONV = RATOR_CONV o RAND_CONV
  open simpLib boolSimps
  fun expand tm =
    ((REWR_CONV RIGHT_AND_OVER_OR THENC BINOP_CONV expand) ORELSEC
     ALL_CONV) tm
  val do_lhs =
    LAND_CONV (BINDER_CONV (LAND_CONV resquan_remove THENC expand) THENC
               SIMP_CONV int_ss [EXISTS_OR_THM]) THENC
    TRY_CONV (REWR_CONV simple_bool_2 ORELSEC REWR_CONV simple_bool_3)
  fun do_rhs tm = let
    val f = if is_disj tm then RAND_CONV
            else if is_exists tm then I
            else K ALL_CONV
    val c =
      STRIP_QUANT_CONV
      (LAND_CONV (RAND_CONV resquan_remove THENC
                  PURE_REWRITE_CONV [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR,
                                     listTheory.MEM, OR_CLAUSES, AND_CLAUSES,
                                     NOT_CLAUSES]) THENC
       expand) THENC
      SIMP_CONV int_ss [EXISTS_OR_THM]
  in
    f c tm
  end
in
  do_lhs THENC do_rhs THENC
  REWRITE_CONV [INT_DIVIDES_1] THENC
  DEPTH_CONV collect_additive_consts
end


fun eliminate_existential tm = let
  val (bvar, body) = dest_exists tm
    handle HOL_ERR _ =>
      raise ERR "eliminate_existential" "term not an exists"
  val base_case =
    BINDER_CONV (phase1_CONV THENC phase2_CONV bvar) THENC
    PURE_REWRITE_CONV [AND_CLAUSES, OR_CLAUSES] THENC
    ((REWR_CONV EXISTS_SIMP THENC REWRITE_CONV []) ORELSEC
     (phase3_CONV THENC phase4_CONV THENC phase5_CONV))
in
  if is_disj body then
    EXISTS_OR_CONV THENC (RAND_CONV eliminate_existential) THENC
    RATOR_CONV (RAND_CONV eliminate_existential)
  else
    base_case
end tm

val NOT_EXISTS_THM =
  GEN_ALL (SYM (PURE_REWRITE_RULE [NOT_CLAUSES]
                (BETA_RULE (Q.SPEC `\x. ~ P x` boolTheory.NOT_EXISTS_THM))))

fun eliminate_quantifier tm = let
  (* assume that there are no quantifiers below the one we're eliminating *)
in
  if is_forall tm then
    Ho_rewrite.REWR_CONV NOT_EXISTS_THM THENC
    PURE_REWRITE_CONV [DE_MORGAN_THM, NOT_CLAUSES, NOT_IMP] THENC
    RAND_CONV eliminate_existential
  else if is_exists tm then
    eliminate_existential
  else if is_uexists tm then
    Ho_rewrite.REWR_CONV EXISTS_UNIQUE_THM THENC
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
  if (is_forall tm orelse is_exists tm orelse is_uexists tm) then
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

val obvious_improvements =
  simpLib.SIMP_CONV int_ss [INT_LT_REFL, INT_NEG_0, INT_DIVIDES_MUL,
                            INT_ADD_LID, INT_ADD_RID, INT_LT_ADD_NUMERAL,
                            INT_LT_LADD]

fun decide_pure_presburger_term tm = let
  (* no free variables allowed *)
in
  case find_low_quantifier tm of
    NONE => REDUCE_CONV
  | SOME f =>
      f eliminate_quantifier THENC obvious_improvements THENC
      decide_pure_presburger_term
end tm


(* good test examples:

   val var = ``x:int``
   fun gen_tm tm0 = let
     val thm1 = (BINDER_CONV (phase1_CONV THENC phase2_CONV var) THENC
                 phase3_CONV) tm0
   in
     rhs (concl thm1)
   end

   val tm = gen_tm ``?x. 2 int_divides x + 1 \/ 3*x < 9 ==> ~(x = 10)``

   open int_arith
   val it0 = ``?x. 2 int_divides x + 1 \/ 3*x < 9 ==> ~(x = 10)``
   val it1 = ``?x:int. x < y``
   val it2 = ``?x:int. 2 * x < 2 * y``
   val it3 = ``?x:int. 4 * x + 3 * y = 10``
   val it4 = ``?x:int. x < y /\ y < z ==> x < z``
   val it5 = ``?x:int. ~(x < y /\ y < z ==> x < z)``
   val it6 = ``?x:int. ~4 int_divides x + 5``
   val it7 = ``?x:int. ~4 int_divides 4 - x``
   val it8 = ``?x:int. x + x = 2 * x``
   val it9 = ``?x:int. y + z = 0n``
   val it10 = ``?y:int. 4 * x + 3 * y = 10``
   val it11 = ``?x:int. x < 3i /\ y:int < z``;

   (* true statements *)
   val pt1 = ``!x:int y z. x < y /\ y < z ==> x < z``
   val pt2 = ``?x y:int. 4 * x + 3 * y = 10``;
   val pt3 = ``!x. 3i * x < 4 * x ==> x > 0``
   val pt4 = ``?y. !x:int. x + y = x``
   val pt5 = ``?y. (!x:int. x + y = x) /\
                   !y'. (!x. x + y' = x) ==> (y = y')``
   val pt6 = ``!x. 3 int_divides x /\ 2 int_divides x ==> 6 int_divides x``
   val pt7 = ``?!y:int. !x. x + y = x``
   val pt8 = ``!x. ?!y. x + y = 0i``
   val pt9 = ``?x y. (x + y = 6i) /\ (2 * x + 3 * y = 11)``
   val pt10 = ``!x z:int. ?!y. x - y = z``
   val pt11 = ``!x y z:int. 2 * x < y /\ y < 2 * z ==>
                            ?w. ((y = 2 * w) \/ (y = 2 * w + 1)) /\
                                x <= w /\ w < z``;


   (* false statements *)
   val fpt1 = ``?x. x * 4 = 6i``
   val fpt2 = ``!x y:int. x < y \/ y < x``
   val fpt3 = ``!x y z:int. 2 * x < y /\ y < 2 * z ==>
                            (y = x + 1) \/ (x < y /\ y < z)``
   val fpt4 = ``?x y:int. 3 * x + 3 * y = 10``;

   fun p15 tm = let
     val (var, _) = dest_exists tm
   in
     (BINDER_CONV (phase1_CONV var THENC phase2_CONV var) THENC
      phase3_CONV THENC phase4_CONV THENC phase5_CONV) tm
   end;

   eliminate_existential it0;
   eliminate_existential it1;
   eliminate_existential it2;
   eliminate_existential it3;
   eliminate_existential it4;
   eliminate_existential it5;
   eliminate_existential it6;
   eliminate_existential it7;
   eliminate_existential it8;
   eliminate_existential it9;
   eliminate_existential it10;
   eliminate_existential it11;

   decide_pure_presburger_term pt1;
   decide_pure_presburger_term pt2;
   decide_pure_presburger_term pt3;
   decide_pure_presburger_term pt4;
   decide_pure_presburger_term pt5;
   decide_pure_presburger_term pt6;
   decide_pure_presburger_term pt7;
   decide_pure_presburger_term pt8;
   decide_pure_presburger_term pt9;
   decide_pure_presburger_term pt10;
   decide_pure_presburger_term pt11;

   decide_pure_presburger_term fpt1;
   decide_pure_presburger_term fpt2;
   decide_pure_presburger_term fpt3;
   decide_pure_presburger_term fpt4;

*)



