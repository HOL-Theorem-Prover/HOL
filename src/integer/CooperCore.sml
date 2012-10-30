structure CooperCore :> CooperCore =
struct
open HolKernel Parse boolLib
     integerTheory int_arithTheory intReduce
     intSyntax CooperSyntax CooperMath CooperThms

val ERR = mk_HOL_ERR "CooperCore";

val lhand = rand o rator

val REWRITE_CONV = GEN_REWRITE_CONV Conv.TOP_DEPTH_CONV bool_rewrites

(* Fix the grammar used by this file *)
structure Parse :> Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars listTheory.list_grammars
end
open Parse

local
  val prove = INST_TYPE [alpha |-> int_ty] o prove
  infix THEN
in

val MEM_base = prove(
  Term`!e:'a l. MEM e (e::l)`,
  REWRITE_TAC [listTheory.MEM]);
val MEM_build = prove(
  Term`!l1 e1:'a e2. MEM e1 l1 ==> MEM e1 (e2::l1)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [listTheory.MEM]);
val mem_nilP = prove(
  ``!P. (?x:'a. MEM x [] /\ P x) = F``,
  REWRITE_TAC [listTheory.MEM]);
val mem_singP = prove(
  ``!P y. (?x:'a. MEM x [y] /\ P x) = P y``,
  simpLib.SIMP_TAC boolSimps.bool_ss [listTheory.MEM]);
val mem_consP = prove(
  ``!P h t. (?x:'a. MEM x (h :: t) /\ P x) = P h \/ (?x. MEM x t /\ P x)``,
  simpLib.SIMP_TAC boolSimps.bool_ss [listTheory.MEM, RIGHT_AND_OVER_OR,
                                      EXISTS_OR_THM]);
end

fun prove_membership t1 t2 = let
  val (tmlist, elty) = listSyntax.dest_list t2
  fun recurse preds thmtodate laters =
    case (thmtodate, preds, laters) of
      (NONE, _, []) => raise ERR "prove_membership" "term not found in list"
    | (NONE, _, x::xs) =>
        if x = t1 then let
          val tailtm = listSyntax.mk_list(xs, elty)
          val whole_list = listSyntax.mk_cons(x, tailtm)
        in
          recurse preds (SOME (ISPECL [x, tailtm] MEM_base, whole_list)) []
        end
        else
          recurse (x::preds) NONE xs
    | (SOME (thm,_), [], _) => thm
    | (SOME (thm,tmlist), p::ps, _) => let
        val newlist = listSyntax.mk_cons(p, tmlist)
        val newthm = MP (ISPECL [tmlist, t1, p] MEM_build) thm
      in
        recurse ps (SOME (newthm, newlist)) []
      end
in
  recurse [] NONE tmlist
end

fun phase4_CONV tm = let
  (* have a formula of the form
       ?x. form
     where
       form ::= form /\ form | form \/ form | ~form | leaf
     and where each leaf either doesn't involve x at all, or is one of
     the following forms:
        x < a,
        b < x,
        x = a,
        d int_divides x + u
     and where all of a, b, u and v are expressions not involving x.
  *)
  val {Bvar, Body} = Rsyntax.dest_exists tm
  val F = rand tm
  val Fx = mk_comb(F, Bvar)
  datatype relntype =
    x_LT of term
  | LT_x of term
  | x_EQ of term
  | DIVIDES of (term * term option)
  fun rtype_to_term rt =
    case rt of
      x_LT t => SOME t
    | LT_x t => SOME t
    | x_EQ t => SOME t
    | _ => NONE
  val leaf_arguments = let
    (* traverse the leaves of the term; classifying all those where the
       Bvar is involved.  If
          x < t    then     add x_LT t
          t < x    then     add LT_x t
          x = t    then     add x_EQ t
          t | x    then     add DIVIDES(t, NONE)
          t | x+a  then     add DIVIDES(t, SOME a)
       Note that t = x never occur because of normalisation carried out
       at the end of phase2.

       Pair these with a boolean indicating the parity
       (true = 0, false = 1) of the number of logical negations passed
       through to get to the leaf.
    *)
    fun recurse posp acc tm = let
      val (l,r) = dest_disj tm
        handle HOL_ERR _ => dest_conj tm
    in
      recurse posp (recurse posp acc r) l
    end handle HOL_ERR _ => let
      val (l,r) = dest_less tm
    in
      if l = Bvar then (x_LT r, posp) :: acc
      else if r = Bvar then (LT_x l, posp) :: acc else acc
    end handle HOL_ERR _ => let
      val (l,r) = dest_eq tm
    in
      if l = Bvar then (x_EQ r, posp) :: acc else acc
    end handle HOL_ERR _ => let
      val (l,r) = dest_divides tm
      val (first_rhs_arg, rest_rhs) = (I ## SOME) (dest_plus r)
        handle HOL_ERR _ => (r, NONE)
    in
      if first_rhs_arg = Bvar then
        (DIVIDES (l, rest_rhs), posp) :: acc
      else acc
    end handle HOL_ERR _ => (* must be a negation *)
      recurse (not posp) acc (dest_neg tm) handle HOL_ERR _ => acc
  in
    Lib.mk_set (recurse true [] Body)
  end
  val use_bis = let
    fun recurse (ai as (a, afv)) (bi as (b, bfv)) l =
      case l of
        [] => (ai, bi)
      | (x_LT tm, true)::t => recurse (a+1, afv + length (free_vars tm)) bi t
      | (x_LT tm, false)::t => recurse ai (b+1, bfv + length (free_vars tm)) t
      | (LT_x tm, true)::t => recurse ai (b+1, bfv + length (free_vars tm)) t
      | (LT_x tm, false)::t => recurse (a+1, afv + length (free_vars tm)) bi t
      | _ :: t => recurse ai bi t
    val ((at,afv), (bt, bfv)) = recurse (0, 0) (0, 0) leaf_arguments
  in
    (bt < at) orelse (bt = at andalso bfv < afv)
  end

  (* need prove either that ?y. !x. x < y ==> (neginf x = F x)  or
     that                   ?y. !x. y < x ==> (posinf x = F x)
     depending on the relative numbers of x_LT and LT_x leaves, i.e.
     our use_bis variable *)
  val lemma = let
    val y = genvar int_ty
    val all_terms = List.mapPartial (rtype_to_term o #1) leaf_arguments
    val MK_LESS = if use_bis then mk_less else (fn (x,y) => mk_less(y,x))
  in
    if null all_terms then let
      (* neginf and F are the same *)
      val without_ex = GEN Bvar (DISCH (MK_LESS(Bvar, y)) (REFL Fx))
    in
      EXISTS (mk_exists(y, concl without_ex), y) without_ex
    end
    else let
      val (minmax_op, minmax_thm, arg_accessor, eqthm_transform) =
        if use_bis then (min_tm, INT_MIN_LT, rand, I)
        else            (max_tm, INT_MAX_LT, lhand, GSYM)
      val witness = let
        fun recurse acc tms =
          case tms of
            [] => acc
          | (x::xs) => recurse (list_mk_comb(minmax_op, [acc, x])) xs
      in
        recurse (hd all_terms) (tl all_terms)
      end
      fun gen_rewrites acc thm =
        if is_conj (concl thm) then
          gen_rewrites (gen_rewrites acc (CONJUNCT1 thm)) (CONJUNCT2 thm)
        else let
          val arg = arg_accessor (concl thm)
          val (hdt, _) = strip_comb arg
        in
          if hdt = minmax_op then
            gen_rewrites acc (MATCH_MP minmax_thm thm)
          else
            EQT_INTRO thm :: EQF_INTRO (MATCH_MP INT_LT_GT thm) ::
            EQF_INTRO (eqthm_transform (MATCH_MP INT_LT_IMP_NE thm)) :: acc
        end
      val rewrites =
        gen_rewrites [] (ASSUME (MK_LESS (Bvar, witness)))
      val thm0 =
        (BETA_CONV THENC REWRITE_CONV rewrites THENC UNBETA_CONV Bvar) Fx
      val thm1 = GEN Bvar (DISCH_ALL thm0)
      val exform = let
        val (x, body) = dest_forall (concl thm1)
        val (_,c) = dest_imp body
        val newh = MK_LESS(x, y)
      in
        mk_exists(y, mk_forall(x, mk_imp(newh, c)))
      end
    in
      EXISTS (exform, witness) thm1
    end
  end
  val neginf = (* call it neginf, though it will be "posinf" if ~ use_bis *)
    rator (rhs (#2 (dest_imp (#2 (dest_forall
                                  (#2 (dest_exists (concl lemma))))))))

  (* before proceeding, need to calculate the LCM of all the d and e of
     the above forms, call it delta *)

  val all_delta_tms = let
    fun collect (DIVIDES(c, _), _) = SOME c
      | collect _ = NONE
  in
    Lib.mk_set (List.mapPartial collect leaf_arguments)
  end
  val all_deltas = map int_of_term all_delta_tms
  val delta = if null all_deltas then Arbint.one else lcml all_deltas
  val delta_tm = term_of_int delta
  val divides_info =
    map (fn ld_tm =>
         (ld_tm, EQT_ELIM (REDUCE_CONV (mk_divides(ld_tm, delta_tm)))))
    all_delta_tms

  (* further need that !x y. neginf x = neginf (x +/- y * delta_tm) *)
  (* The argument to neginf only appears as argument to divides terms.
     We must be able to reduce
       c int_divides (x +/- y * delta + e)   to
       c int_divides (x + e)
     given that c is a divisor of delta.  We first reduce
       (x +/- y + e) to (x + e +/- y)
     using either the theorem move_sub or move_add (proved above).
     Then we have
       c int_divides y ==> (c int_divides (x +/- y) = c int_divides x)  and
       c int_divides x ==> c int_divides (x * y)
     which we specialise with the appropriate values for x and y, and then
     use rewriting to do the right reductions
  *)
  val lemma2 = let
    val y = genvar int_ty
    val (tm0, move_thm, divides_thm) =
      if use_bis then (mk_comb (neginf, mk_minus(Bvar, mk_mult(y, delta_tm))),
                       move_sub, INT_DIVIDES_RSUB)
      else (mk_comb (neginf, mk_plus(Bvar, mk_mult(y, delta_tm))),
            move_add, INT_DIVIDES_RADD)
    fun recurse tm =
      if is_conj tm orelse is_disj tm then
        BINOP_CONV recurse tm
      else if is_neg tm then
        RAND_CONV recurse tm
      else let
        val (local_delta, arg2) = dest_divides tm
        val (l,r) = dest_plus arg2
          handle (e as HOL_ERR _) => if use_bis then dest_minus arg2
                                     else raise e
      in
        if l = Bvar then let
          (* the original divides term is of form c | x *)
          val ldel_divides = Lib.assoc local_delta divides_info
          val ldel_divides_dely =
            SPEC y (MATCH_MP INT_DIVIDES_RMUL ldel_divides)
          val ldel_simpler = MATCH_MP divides_thm ldel_divides_dely
        in
          REWR_CONV ldel_simpler tm
        end
        else let
          val (ll, lr) = (if use_bis then dest_minus else dest_plus) l
          val _ = ll = Bvar orelse raise ERR "" ""
          (* the original divides term of form c | x + e            *)
          (* we're rewriting something like c | (x +/- y * d) + e   *)
          val ldel_divides = Lib.assoc local_delta divides_info
          val ldel_divides_dely =
            SPEC y (MATCH_MP INT_DIVIDES_RMUL ldel_divides)
          val ldel_simpler = MATCH_MP divides_thm ldel_divides_dely
        in
          (RAND_CONV (REWR_CONV move_thm) THENC
           REWR_CONV ldel_simpler) tm
        end
      end handle HOL_ERR _ => ALL_CONV tm
    val c =
      BETA_CONV THENC recurse THENC UNBETA_CONV Bvar
  in
    GENL [y, Bvar] (c tm0)
  end

  val disj1 = let
    val i = genvar int_ty
    val restriction = mk_conj(mk_less(zero_tm, i),
                              mk_leq(i, delta_tm))
  in
    mk_exists(i, mk_conj(restriction, mk_comb(neginf, i)))
  end

  val (disj2, bis_list_tm) = let
    (* need all of the bi *)
    val intlist_ty = mk_thy_type{Args=[int_ty], Tyop="list",Thy="list"}
    fun find_bi (LT_x t, true) = SOME t
      | find_bi (x_LT t, false) = SOME (mk_plus(t, mk_negated one_tm))
      | find_bi (x_EQ t, true) = SOME (mk_plus(t, mk_negated one_tm))
      | find_bi (x_EQ t, false) = SOME t
      | find_bi _ = NONE
    fun find_ai (x_LT t, true) = SOME t
      | find_ai (LT_x t, false) = SOME (mk_plus(t, one_tm))
      | find_ai (x_EQ t, true) = SOME (mk_plus(t, one_tm))
      | find_ai (x_EQ t, false) = SOME t
      | find_ai _ = NONE
    val (find_xi, arith_op) = if use_bis then (find_bi, mk_plus)
                              else (find_ai, mk_minus)
    val bis = Lib.mk_set (List.mapPartial find_xi leaf_arguments)
    val bis_list_tm = listSyntax.mk_list(bis, int_ty)
    val b = genvar int_ty
    val j = genvar int_ty
    val brestriction = listSyntax.mk_mem(b, bis_list_tm)
    val jrestriction = mk_conj(mk_less(zero_tm, j), mk_leq(j, delta_tm))
  in
    (list_mk_exists([b,j], mk_conj(mk_conj(brestriction, jrestriction),
                                   mk_comb(F, arith_op(b,j)))),
     bis_list_tm)
  end

  (* now must prove that (?x. F x) = disj1 \/ disj2 *)
  (* first show disj1 ==> (?x. F x) *)

  (* Comments true for use_bis = true.  Proof strategy for use_bis = false
     is the same; we just substitute can_get_big for can_get_small at
     the crucial moment.

     we have
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
  val delta_ok = CONJ zero_lt_delta (SPEC delta_tm INT_LE_REFL)
  val one_ok =
    EQT_ELIM (REDUCE_CONV (mk_conj(mk_less(zero_tm, one_tm),
                                   mk_leq(one_tm, delta_tm))))
  val disj1_implies_exFx = let
    val (disj1_var, disj1_body) = dest_exists disj1
    val assumption0 = ASSUME disj1_body
    val assumption = CONJUNCT2 assumption0
    val lemma_var = genvar int_ty
    val thm1 = let
      val (exvar, lemma_body) = dest_exists (concl lemma)
    in
      ASSUME (subst [exvar |-> lemma_var] lemma_body)
    end
    val c = rand (concl assumption)
    val spec_cgs =
      SPECL [lemma_var, c, delta_tm] (if use_bis then can_get_small
                                      else can_get_big)
    val thm0 = MP spec_cgs zero_lt_delta
    val e = genvar int_ty
    val thm2 = let
      val (v, body) = dest_exists (concl thm0)
    in
      CONJUNCT2 (ASSUME (subst [v |-> e] body))
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
        end else if is_neg thm then let
           val Pxd_tm = dest_neg tm
           val subres = recurse (ASSUME Pxd_tm) (dest_neg (concl thm))
           val false_concl = MP thm subres
        in
           EQF_ELIM (DISCH Pxd_tm false_concl)
        end

    There are seven base cases depending on the form of the term and
    whether or not we're under a negation; the following are
    demonstrate what happens when use_bis is true.

         (A)   thm  = |- x < e
               tm   =    x - d < e
               posp = true

              0 < d              (zero_lt_delta)
           specialise INT_LT_ADD2 with x, e, 0, d to get
              x < e /\ 0 < d ==> x + 0 < e + d
           discharge with conjunction of thm and zero_lt_delta to get
              x + 0 < e + d
           CONV_RULE (RATOR_CONV (RAND_CONV (REWR_CONV INT_ADD_RID))) to get
              x < e + d
           CONV_RULE (REWR_CONV (GSYM INT_LT_SUB_RADD)) to get
              x - d < e
           as required

         (B)   thm  = |- x - d < e
               tm   = |- x < e
               posp = false

           e + ~1 is one of the bi terms

           ASSUME ~tm
                     |- ~(x < e)
           REWR_CONV with not_less
                     |- e < x + 1
           REWR_CONV with (GSYM INT_LT_ADDNEG2)
                     |- e + ~1 < x                  (lowbound)
           REWR_CONV thm with less_to_leq_samel
                     |- x - d <= e + ~1
           REWR_CONV with INT_LE_SUB_RADD
                     |- x <= (e + ~1) + d           (highbound)
           REWR_CONV (lowbound /\ highbound) with in_additive_range
                     |- ?j. (x = (e + ~1) + j) /\ 0 < j /\ j <= d
           choose j take conjuncts
                     |- (x = (e + ~1) + j)          (conj1)
                     |- 0 < j /\ j <= d             (conj2)
           prove e + ~1 in list of bis              (membership)
           match not_thm with membership /\ conj2
                     |- ~P((e + ~1) + j)            (notP)
           AP_TERM P conj1
                     |- P(x) = P((e + ~1) + j)
           EQ_TRANS with fx_thm
                     |- P((e + ~1) + j)
           MP with notP
                     |- F
           CCONTR tm
                     |- x < e    as required

         (C)   thm  = |- e < x
               tm   =    e < x - d
               posp = true

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

         (D)   thm  = |- e < x - d
               tm   = |- e < x
               posp = false


                      |- 0 < d                  (zero_lt_delta)
               REWR_CONV (GSYM INT_NEG_LT0)
                      |- ~d < 0                 (part2)
               REWR_CONV INT_LT_SUB_LADD thm
                      |- e + d < x              (part1)
               MATCH_MP INT_LT_ADD2 (part1 /\ part2)
                      |- e + d + ~d < x + 0
               CONV_RULE (LAND_CONV (REWR_CONV (GSYM INT_ADD_ASSOC)))
                      |- e + (d + ~d) < x + 0
               CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV INT_ADD_RINV)))
                      |- e + 0 < x + 0
               CONV_RULE (BINOP_CONV (REWR_CONV INT_ADD_RID))
                      |- e < x

         (E)

             thm  =  |- x = e
             tm   =     x - d = e
             posp =  true

             given our assumption, the thm is an impossibility
             straightaway.

             specialise not_thm with e + ~1 and 1 to get
                    |- MEM (e + ~1) [...] /\ 0 < 1 /\ 1 <= d ==>
                       ~F(e + ~1 + 1)                     (spec_not_thm)
             prove e + ~1 is in list of bis
                    |- MEM (e + ~1) [b1; b2; ... bn]      (membership)
             prove arithmetics of 1 with REDUCE_CONV
                    |- 0 < 1 /\ 1 <= d                    (one_ok)
             match membership /\ one_ok against spec_not_thm to get
                    |- ~F(e + ~1 + 1)                     (not_f_11)
             EQF_INTRO not_f_11
                    |- F (e + ~1 + 1) = F                 (f_11_eqF)
             SYM (SPEC e elim_neg_ones)
                    |- e = e + ~1 + 1                     (e_eq_11)
             TRANS thm e_eq_11
                    |- x = e + ~1 + 1                     (x_eq_11)
             AP_TERM F x_eq_11
                    |- F(x) = F(e + ~1 + 1)               (Fx_eq_Fe_11)
             TRANS Fx_eq_Fe_11 f_11_eqF
                    |- F(x) = F                           (Fx_eq_F)
             EQ_MP fx_thm Fx_eq_F
                    |- F
             CONTR tm
                    |- x - d = e     as required

         (F)
             thm  = |- x - d = e
             tm   =    x = e
             posp = false

             e is in bis list

             thm
                   |- x - d = e                           (xlessd_eq_e)
             CONV_RULE (REWR_CONV INT_EQ_SUB_RADD)
                   |- x = e + d                           (x_eq_ed)
             SPECL [e, d] not_thm
                   |- MEM e [...] /\ 0 < d /\ 1 <= d ==>
                      ~F(e + d)                           (spec_not_thm)
             prove e is in list of bis
                   |- MEM e [b1;b2;... bn]                (membership)
             MP spec_not_thm (CONJ membership delta_ok)
                   |- ~F(e + d)                           (not_fed)
             EQF_INTRO not_fed
                   |- F(e + d) = F                        (fed_eq_f)
             AP_TERM F x_eq_ed
                   |- F(x) = F(e + d)                     (fx_eq_fed)
             TRANS fx_eq_fed fed_eq_f
                   |- F(x) = F                            (fx_eq_f)
             EQ_MP fx_thm fx_eq_f
                   |- F
             CCONTR tm
                   |- x = e

         (G)

              thm  = |- f int_divides (x + e)
              tm   =    f int_divides (x - d + e)
              posp = _

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
    exception UnexpectedTerm of term
    val fx_goes_downward = let
      (* to prove either ~disj2 |- !x. F x ==> F (x - d)   (use_bis) or
                         ~disj2 |- !x. F x ==> F (x + d)   (~use_bis) *)
      val not_disj2_0 = mk_neg disj2
      val not_disj2_thm = ASSUME not_disj2_0
      val not_thm =
        CONV_RULE (NOT_EXISTS_CONV THENC
                   BINDER_CONV NOT_EXISTS_CONV THENC
                   STRIP_QUANT_CONV (REWR_CONV NOT_AND_IMP))
        not_disj2_thm
      val fx_thm = ASSUME (mk_comb(F, Bvar))
      val fx_thm_expanded = CONV_RULE BETA_CONV fx_thm
      fun arecurse posp thm tm = let
        val thm_concl = concl thm
      in let
        val (c1, c2) = dest_conj tm
      in
        CONJ (arecurse posp (CONJUNCT1 thm) c1)
             (arecurse posp (CONJUNCT2 thm) c2)
      end handle HOL_ERR _ => let
        val (d1_thm0, d2_thm0) = (ASSUME ## ASSUME) (dest_disj thm_concl)
        val (d1_tm, d2_tm) = dest_disj tm
        val d1_thm = DISJ1 (arecurse posp d1_thm0 d1_tm) d2_tm
        val d2_thm = DISJ2 d1_tm (arecurse posp d2_thm0 d2_tm)
      in
        DISJ_CASES thm d1_thm d2_thm
      end handle HOL_ERR _ => let
        val Pxd_tm = dest_neg tm
        val subres = arecurse (not posp) (ASSUME Pxd_tm) (dest_neg (concl thm))
        val false_concl = MP thm subres
      in
        NOT_INTRO (DISCH Pxd_tm false_concl)
      end handle HOL_ERR _ => let
        val (lthm,rthm) = dest_less thm_concl
        val (ltm, rtm) = dest_less tm
      in
        (* base cases with less as operator *)
        if posp then (* thm is positive instance *)
          if lthm = Bvar then let
            (* x < e - want to prove that x + d < e
               do it by contradiction *)
            val e = rthm
            val not_tm = ASSUME (mk_neg tm)
            val leq_var = CONV_RULE (REWR_CONV INT_NOT_LT THENC
                                     REWR_CONV (GSYM INT_LE_SUB_RADD)) not_tm
            (* ~(x + d < e) --> e <= x + d --> e - d <= x *)
            val exists_j0 =
              CONV_RULE (REWR_CONV in_subtractive_range) (CONJ leq_var thm)
            val exists_j =
                EQ_MP (GEN_ALPHA_CONV (genvar int_ty) (concl exists_j0))
                      exists_j0
            (* ?j. (x = e - j) /\ 0 < j /\ j <= d *)
            val membership = prove_membership e bis_list_tm
            val (jvar, jbody) = dest_exists (concl exists_j)
            val choose_j = ASSUME jbody
            val (var_eq, j_in_range) = CONJ_PAIR choose_j
            val not_fej =
              EQF_INTRO (MATCH_MP not_thm (CONJ membership j_in_range))
            val fx_eq_fej = AP_TERM F var_eq
            val fx_eq_F = TRANS fx_eq_fej not_fej
            val contradiction = EQ_MP fx_eq_F fx_thm
          in
            CCONTR tm (CHOOSE(jvar, exists_j) contradiction)
          end
          else if rthm = Bvar then let
            val e = lthm
            (* e < x - want to prove e < x + d *)
            val thm0 = SPECL [e, Bvar, zero_tm, delta_tm] INT_LT_ADD2
            (* e < x /\ 0 < d ==> e + 0 < x + d *)
            val thm1 = MP thm0 (CONJ thm zero_lt_delta)
          (* e + 0 < x + d *)
          in
            CONV_RULE (LAND_CONV (REWR_CONV INT_ADD_RID)) thm1
          end
          else (* Bvar not present *) thm
        else (* not posp *)
          if ltm = Bvar then let
            (* have x + d < e, want to show x < e *)
            val negdelta_lt_0 =
              CONV_RULE (REWR_CONV (GSYM INT_NEG_LT0)) zero_lt_delta
            val stage0 =
              MATCH_MP INT_LT_ADD2 (CONJ thm negdelta_lt_0)
              (* (x + d) + ~d < e + 0 *)
            val stage1 =
              CONV_RULE (LAND_CONV (REWR_CONV (GSYM INT_ADD_ASSOC))) stage0
              (* x + (d + ~d) < e + 0 *)
            val stage2 =
              CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV INT_ADD_RINV))) stage1
              (* x + 0 < e + 0 *)
          in
            CONV_RULE (BINOP_CONV (REWR_CONV INT_ADD_RID)) stage2
          end
          else if rtm = Bvar then let
            val e = ltm
            (* have e < x + d, want to show e < x  -- by contradiction *)
            val not_tm = ASSUME (mk_neg tm)
              (* |- ~(e < x) *)
            val x_lt_e1 = CONV_RULE (REWR_CONV not_less) not_tm
              (* |- x < e + 1 *)
            val e1_leq_xd = CONV_RULE (REWR_CONV less_to_leq_samer) thm
              (* |- e + 1 <= x + d *)
            val e1d_leq_x =
              CONV_RULE (REWR_CONV (GSYM INT_LE_SUB_RADD)) e1_leq_xd
              (* |- (e + 1) - d <= x *)
            val exists_j0 =
              CONV_RULE (REWR_CONV in_subtractive_range)
                        (CONJ e1d_leq_x x_lt_e1)
            val exists_j =
                EQ_MP (GEN_ALPHA_CONV (genvar int_ty) (concl exists_j0))
                      exists_j0
              (* ?j. (x = e + 1 - j) /\ 0 < j /\ j <= d *)
            val membership = prove_membership (mk_plus(e,one_tm)) bis_list_tm
            val (jvar, jbody) = dest_exists (concl exists_j)
            val choose_j = ASSUME jbody
            val (var_eq, j_in_range) = CONJ_PAIR choose_j
            val not_fej = MATCH_MP not_thm (CONJ membership j_in_range)
            val fej = EQ_MP (AP_TERM F var_eq) fx_thm
          in
            CCONTR tm (CHOOSE(jvar, exists_j) (MP not_fej fej))
          end
          else (* Bvar not present *) thm
      end handle HOL_ERR _ => let
        val (lthm,rthm) = dest_eq thm_concl
        val (ltm, rtm) = dest_eq tm
      in
        if posp then
          if lthm = Bvar then let
            (* x = e *)
            val e = rthm
            val e_plus_1 = mk_plus(e, one_tm)
            val spec_not_thm = SPECL [e_plus_1, one_tm] not_thm
            (* MEM (e + 1) [....; e + 1] /\ 0 < 1 /\ 1 <= d ==>
               ~F(e + 1 - 1) *)
            val membership = prove_membership e_plus_1 bis_list_tm
            val not_fe1 = MP spec_not_thm (CONJ membership one_ok)
            val fe1_eqF = EQF_INTRO not_fe1
            (* F(e + 1 - 1) = false *)
            val e_eq_e11 = SYM (SPEC e elim_minus_ones)
            (* e = e + 1 - 1 *)
            val x_eq_e11 = TRANS thm e_eq_e11
            (* x = e + 1 - 1 *)
            val Fx_eq_Fe11 = AP_TERM F x_eq_e11
            (* F x = F(e + 1 - 1) *)
            val Fx_eq_F = TRANS Fx_eq_Fe11 fe1_eqF
          in
            CONTR tm (EQ_MP Fx_eq_F fx_thm)
          end
          else (* Bvar not present *)
            thm
        else (* not posp *)
          if ltm = Bvar then let
            (* have x + d = e, want x = e *)
            val e = rtm
            val xplusd_eq_e = thm
            val x_eq_elessd =
              EQ_MP (SYM (SPECL [Bvar,e,delta_tm] INT_EQ_SUB_LADD)) xplusd_eq_e
              (* x = e - d *)
            val F_elessd = EQ_MP (AP_TERM F x_eq_elessd) fx_thm
            val spec_not_thm = SPECL [e, delta_tm] not_thm
            val membership = prove_membership e bis_list_tm
            val not_F_elessd = MP spec_not_thm (CONJ membership delta_ok)
          in
            CCONTR tm (MP not_F_elessd F_elessd)
          end
          else (* Bvar not present *) thm
      end handle HOL_ERR _ => let
        val (c,r) = dest_divides (if posp then thm_concl else tm)
        val (var, rem) = (I ## SOME) (dest_plus r)
          handle HOL_ERR _ => (r, NONE)
      in
        if var = Bvar then let
          (* c | x [+ rem] - want to show that c | x + d [ + rem ] *)
          val c_div_d = Lib.assoc c divides_info
          val c_div_rplusd0 =
            SYM (MP (SPECL [c,delta_tm,r] INT_DIVIDES_RADD) c_div_d)
          (* c | x [+ rem] = c | x [+ rem] + d *)
          val c_div_rplusd1 =
            if isSome rem then
              CONV_RULE (RAND_CONV
                         (RAND_CONV (REWR_CONV move_add))) c_div_rplusd0
            else c_div_rplusd0
          val c_div_rplusd = if posp then c_div_rplusd1 else SYM c_div_rplusd1
        in
          EQ_MP c_div_rplusd thm
        end
        else thm
      end handle HOL_ERR _ =>
                 if is_constraint tm then thm
                 else raise UnexpectedTerm tm
      end (* need double end, because of double let at start of function *)

      fun brecurse posp thm tm = let
        val thm_concl = concl thm
      in let
        val (c1, c2) = dest_conj tm
      in
        CONJ (brecurse posp (CONJUNCT1 thm) c1)
             (brecurse posp (CONJUNCT2 thm) c2)
      end handle HOL_ERR _ => let
        val (d1_thm0, d2_thm0) = (ASSUME ## ASSUME) (dest_disj (concl thm))
        val (d1_tm, d2_tm) = dest_disj tm
        val d1_thm = DISJ1 (brecurse posp d1_thm0 d1_tm) d2_tm
        val d2_thm = DISJ2 d1_tm (brecurse posp d2_thm0 d2_tm)
      in
        DISJ_CASES thm d1_thm d2_thm
      end handle HOL_ERR _ => let
        val Pxd_tm = dest_neg tm
        val subres = brecurse (not posp) (ASSUME Pxd_tm) (dest_neg (concl thm))
        val false_concl = MP thm subres
      in
        NOT_INTRO (DISCH Pxd_tm false_concl)
      end handle HOL_ERR _ => let
        val (lthm,rthm) = dest_less thm_concl
        val (ltm, rtm) = dest_less tm
      in
        (* base cases with less as operator *)
        if posp then
          if lthm = Bvar then let
            (* x < e *)
            val e = rthm
            val thm0 = SPECL [Bvar, e, zero_tm, delta_tm] INT_LT_ADD2
            val thm1 = MP thm0 (CONJ thm zero_lt_delta)
            val thm2 =
              CONV_RULE (LAND_CONV (REWR_CONV INT_ADD_RID)) thm1
          in
            CONV_RULE (REWR_CONV (GSYM INT_LT_SUB_RADD)) thm2
          end
          else if rthm = Bvar then let
            (* e < x *)
            val e = lthm
            val not_tm = ASSUME (mk_neg tm)
            val var_leq = CONV_RULE (REWR_CONV INT_NOT_LT THENC
                                     REWR_CONV INT_LE_SUB_RADD) not_tm
            val exists_j0 =
              CONV_RULE (REWR_CONV in_additive_range) (CONJ thm var_leq)
            val exists_j =
                EQ_MP (GEN_ALPHA_CONV (genvar int_ty) (concl exists_j0))
                      exists_j0
            val membership = prove_membership e bis_list_tm
            (* choose j from exists_j *)
            val (jvar, jbody) = dest_exists (concl exists_j)
            val choose_j = ASSUME jbody
            val (var_eq, j_in_range) = CONJ_PAIR choose_j
            val not_fej =
              EQF_INTRO (MATCH_MP not_thm (CONJ membership j_in_range))
            val fx_eq_fej = AP_TERM F var_eq
            val fx_eq_F = TRANS fx_eq_fej not_fej
            val contradiction = EQ_MP fx_eq_F fx_thm
          in
            CCONTR tm (CHOOSE(jvar, exists_j) contradiction)
          end
          else (* Bvar not present *) thm
        else (* not posp *)
          if ltm = Bvar then let
            val e = rtm
            (* have x - d < e, want x < e  - by contradiction *)
            val not_tm = ASSUME (mk_neg tm)
            val e_less_x1 = CONV_RULE (REWR_CONV not_less) not_tm
              (* e < x + 1 *)
            val lobound = CONV_RULE (REWR_CONV (GSYM INT_LT_ADDNEG2)) e_less_x1
              (* e + ~1 < x *)
            val xd_leq_e1 = CONV_RULE (REWR_CONV less_to_leq_samel) thm
              (* x - d <= e + ~1 *)
            val hibound = CONV_RULE (REWR_CONV INT_LE_SUB_RADD) xd_leq_e1
              (* x <= e + ~1 + d *)
            val exists_j0 =
              CONV_RULE (REWR_CONV in_additive_range) (CONJ lobound hibound)
            val exists_j =
                EQ_MP (GEN_ALPHA_CONV (genvar int_ty) (concl exists_j0))
                      exists_j0
            val membership =
              prove_membership (mk_plus(e,mk_negated one_tm)) bis_list_tm
            val (jvar, jbody) = dest_exists (concl exists_j)
            val choose_j = ASSUME jbody
            val (var_eq, j_in_range) = CONJ_PAIR choose_j
            val not_fej = MATCH_MP not_thm (CONJ membership j_in_range)
            val fej = EQ_MP (AP_TERM F var_eq) fx_thm
          in
            CCONTR tm (CHOOSE(jvar, exists_j) (MP not_fej fej))
          end
          else if rtm = Bvar then let
            (* have e < x - d, want e < x *)
            val ed_lt_x = CONV_RULE (REWR_CONV INT_LT_SUB_LADD) thm
            (* have e + d < x, want to show e < x *)
            val negdelta_lt_0 =
              CONV_RULE (REWR_CONV (GSYM INT_NEG_LT0)) zero_lt_delta
            val stage0 =
              MATCH_MP INT_LT_ADD2 (CONJ ed_lt_x negdelta_lt_0)
              (* (e + d) + ~d < x + 0 *)
            val stage1 =
              CONV_RULE (LAND_CONV (REWR_CONV (GSYM INT_ADD_ASSOC))) stage0
              (* e + (d + ~d) < x + 0 *)
            val stage2 =
              CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV INT_ADD_RINV))) stage1
              (* e + 0 < x + 0 *)
          in
            CONV_RULE (BINOP_CONV (REWR_CONV INT_ADD_RID)) stage2
          end else (* Bvar not here *) thm
      end handle HOL_ERR _ => let
        val (lthm, rthm) = dest_eq thm_concl
        val (ltm, rtm) = dest_eq tm
      in
        if posp then
          if lthm = Bvar then let
            (* have x = e, want to show x - d = e *)
            val e = rtm
            val e_less1 = mk_plus(e, mk_negated one_tm)
            val spec_not_thm = SPECL [e_less1, one_tm] not_thm
            val membership = prove_membership e_less1 bis_list_tm
            val not_f_11 = MP spec_not_thm (CONJ membership one_ok)
            val f_11_eqF = EQF_INTRO not_f_11
            val e_eq_11 = SYM (SPEC e elim_neg_ones)
            val x_eq_11 = TRANS thm e_eq_11
            val Fx_eq_Fe_11 = AP_TERM F x_eq_11
            val Fx_eq_F = TRANS Fx_eq_Fe_11 f_11_eqF
          in
            CONTR tm (EQ_MP Fx_eq_F fx_thm)
          end
          else thm
        else (* not posp *)
          if ltm = Bvar then let
            (* have x - d = e, want to show x = e *)
            val e = rthm
            val xlessd_eq_e = thm
            val x_eq_ed = CONV_RULE (REWR_CONV INT_EQ_SUB_RADD) xlessd_eq_e
            val spec_not_thm = SPECL [e, delta_tm] not_thm
            val membership = prove_membership e bis_list_tm
            val not_fed = MP spec_not_thm (CONJ membership delta_ok)
            val fed = EQ_MP (AP_TERM F x_eq_ed) fx_thm
          in
            CCONTR tm (MP not_fed fed)
          end
          else thm
      end handle HOL_ERR _ => let
        val (c,r) = dest_divides (if posp then thm_concl else tm)
        val (var, rem) = (I ## SOME) (dest_plus r)
          handle HOL_ERR _ => (r, NONE)
      in
        if var = Bvar then let
          (* c | x [+ rem] - want to show that c | x + d [ + rem ] *)
          val c_div_d = Lib.assoc c divides_info
          val c_div_rsubd0 =
            MP (SPECL [c,delta_tm,r] INT_DIVIDES_RSUB) c_div_d
          (* c | x [+ rem] = c | x [+ rem] + d *)
          val c_div_rsubd1 =
            if isSome rem then
              CONV_RULE (LAND_CONV
                         (RAND_CONV (REWR_CONV (GSYM move_sub)))) c_div_rsubd0
            else c_div_rsubd0
          val c_div_rsubd = if posp then SYM c_div_rsubd1 else c_div_rsubd1
        in
          EQ_MP c_div_rsubd thm
        end
        else thm
      end handle HOL_ERR _ =>
                 if is_constraint tm then thm
                 else raise UnexpectedTerm tm
      end (* again need a double end *)


      val (arith_op, recurse) =
        if use_bis then (mk_minus, brecurse) else (mk_plus, arecurse)
      val fxd_beta_thm = BETA_CONV (mk_comb(F, arith_op(Bvar, delta_tm)))
      val fxd_tm = rhs (concl fxd_beta_thm)
      val fxd_thm = recurse true fx_thm_expanded fxd_tm
                    handle UnexpectedTerm tm =>
                           raise ERR "phase4_CONV"
                                     ("Unexpected term: "^term_to_string tm)
    in
      GEN Bvar (DISCH Fx (EQ_MP (SYM fxd_beta_thm) fxd_thm))
    end
    val x0 = genvar int_ty
    val Fx0 = mk_comb(F, x0)
    val Fx0_thm = ASSUME Fx0
    val (change_by_dmultiples, can_become_extreme, change_to_extreme) =
      if use_bis then
        (MP (SPECL [F, delta_tm, x0] top_and_lessers)
         (CONJ fx_goes_downward Fx0_thm),
         can_get_small,
         subtract_to_small)
      else
        (MP (SPECL [F, delta_tm, x0] bot_and_greaters)
         (CONJ fx_goes_downward Fx0_thm), can_get_big,
         add_to_great)
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
      ASSUME (subst [exvar |-> y] exbody)
    end
    (*
       specialise can_get_small with [y, x0, d] and MP with zero_lt_delta
          (little_c_ex)    |- ?c. 0 < c /\ x0 - c * d < y
    *)
    val little_c_ex =
      MP (SPECL [y, x0, delta_tm] can_become_extreme) zero_lt_delta
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
      ASSUME (subst [exvar |-> u] exbody)
    end
    val zero_lt_u = CONJUNCT1 choose_u
    val x0_less_ud = CONJUNCT2 choose_u
    (*
       SPEC change_by_dmultiples with u, and MP with zero_lt_u to get
          (Fx0_less_ud)   . |- F (x0 - u * d)
    *)
    val Fx0_less_ud = MP (SPEC u change_by_dmultiples) zero_lt_u
    (* SPEC choose_lemma with x0 - u * d and MP with x0_less_ud to get
     (Fneginf_x0_less_ud) . |- F (x0 - u * d) = neginf (x0 - u * d)
    *)
    val x0_less_ud_tm = if use_bis then lhand (concl x0_less_ud)
                        else rand (concl x0_less_ud)
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
      MP (SPECL [x0_less_ud_tm, delta_tm] change_to_extreme) zero_lt_delta
    (*
       choose k, to get
         (choose_k)         |- 0 < x0 - u * d - k * d /\ x0 - u*d - k*d <= d
    *)
    val k = genvar int_ty
    val choose_k = let
      val (exvar, exbody) = dest_exists (concl exists_small_k)
    in
      ASSUME (subst [exvar |-> k] exbody)
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
    CONV_RULE (LAND_CONV (BINDER_CONV BETA_CONV)) (DISCH_ALL res4)
  end
  val thm0 = IMP_ANTISYM_RULE exFx_implies_rhs rhs_implies_exFx
  val neginf_constrain = BINDER_CONV (LAND_CONV MK_CONSTRAINT)
  val rhs_constrain  = BINDER_CONV (LAND_CONV (RAND_CONV MK_CONSTRAINT))
in
  CONV_RULE (RAND_CONV                (* on rhs *)
             (LAND_CONV neginf_constrain THENC
              RAND_CONV (BINDER_CONV rhs_constrain))) thm0
end

(*
val phase4_CONV = Profile.profile "phase4" phase4_CONV
*)

fun LIST_EL_CONV c tm = let
  (* applies c to all elements of a literal list tm *)
  val (f, args) = strip_comb tm
in
  case args of
    [] => (* nil case *) ALL_CONV tm
  | h::t => (* h the element, t the tail of the list *)
      (LAND_CONV c THENC RAND_CONV (LIST_EL_CONV c)) tm
end


fun in_list_CONV tm = let
  val (v, body) = dest_exists tm
  val (mem_t, _) = dest_conj body
  val (_, list_t) = listSyntax.dest_mem mem_t

  fun recurse tm = let
    val (v, body) = dest_exists tm
    val (mem_t, _) = dest_conj body
    val (_, list_t) = listSyntax.dest_mem mem_t
    (* mem_t = MEM v l and l is not nil, so list_t = CONS h t *)
  in
    if is_const (rand list_t) then REWR_CONV mem_singP
    else REWR_CONV mem_consP THENC RAND_CONV recurse
  end tm
in
  if is_const list_t (* i.e. = [] *) then REWR_CONV mem_nilP tm
  else recurse tm
end



fun elim_bterms tm = let
  (* tm is of form
        ?b. (MEM b list /\ K ... j) /\ f (b + j)
     or
        ?b. MEM b list /\ f (b + j)
  *)
  val (var, body) = dest_exists tm
  val initially = if is_conj (lhand body) then REWR_CONV (GSYM CONJ_ASSOC)
                  else ALL_CONV
in
  BINDER_CONV (RAND_CONV BETA_CONV THENC initially THENC
               (*Profile.profile "eb.abs"*) (RAND_CONV (UNBETA_CONV var))) THENC
  (*Profile.profile "eb.in_list"*) in_list_CONV THENC
  (*Profile.profile "eb.beta"*) (EVERY_DISJ_CONV (TRY_CONV BETA_CONV))
end tm





val phase5_CONV  = let
  (* have something of the form
       (?x. K (0 < x /\ x <= k) x  /\ neginf x) \/
       (?b k. (MEM b [..] /\ K (0 < k /\ k <= d) k) /\ F (b + k))
  *)
  val prelim_left = BINDER_CONV (RAND_CONV BETA_CONV)
  val prelim_right =
    STRIP_QUANT_CONV
    (RAND_CONV (RAND_CONV
                  (* turn minus terms F (b - k) into F (b + ~1 * k) *)
                (fn t => if is_minus t then
                           (REWR_CONV int_sub THENC
                            RAND_CONV (REWR_CONV INT_NEG_MINUS1)) t
                         else ALL_CONV t)) THENC
     (* collect additive consts on elements of list *)
     LAND_CONV (LAND_CONV (* first conjunct of three *)
                    (RAND_CONV (* set [...] (from b ∈ set [..]) *)
                         (RAND_CONV (* [...] *)
                              (LIST_EL_CONV
                                   (TRY_CONV collect_additive_consts))))))



  val elim_bterms_on_right =
    (* the second disjunct produced by phase4 is of form
          ?b k. (MEM b [...] /\ K (lo < k /\ k <= hi) k) /\ F(b + k) *)
    (* first try eliminating trivial constraints on k *)
    TRY_CONV (STRIP_QUANT_CONV (LAND_CONV (RAND_CONV quick_cst_elim)) THENC
              (BINDER_CONV Unwind.UNWIND_EXISTS_CONV ORELSEC
               REWRITE_CONV [])) THENC
    (* at this stage, k may or may not have been eliminated by the previous
       step, either by becoming false, which will have already turned the
       whole term false, or by becoming unwound.
       In the former, the TRY_CONV will do nothing because the LAND_CONV
       will fail.
       Otherwise, the basic action here is to expand out all of the
       "b" possibilities in the list *)
    TRY_CONV (((SWAP_VARS_CONV THENC BINDER_CONV elim_bterms) ORELSEC
               elim_bterms) THENC
              reduce_if_ground THENC
              push_one_exists_over_many_disjs)
  (*
  val elim_bterms_on_right = Profile.profile "phase5.er" elim_bterms_on_right
  *)
in
  LAND_CONV prelim_left THENC
  RAND_CONV (prelim_right THENC elim_bterms_on_right) THENC
  EVERY_DISJ_CONV (TRY_CONV fixup_newvar THENC
                   ONCE_DEPTH_CONV check_divides THENC
                   TRY_CONV simplify_constrained_disjunct THENC
                   TRY_CONV (REWR_CONV EXISTS_SIMP))
end

(*
val phase5_CONV = Profile.profile "phase5" phase5_CONV
*)

end
