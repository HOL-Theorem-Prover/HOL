(* Quickcheck generator and compset fragment for :rat.

   Candidates and goal literals alike decide, via proof-time conversions
   (ratLib.RAT_CALC_CONV / fracLib.FRAC_CALC_CONV plus arithmetic
   side-condition discharge), to abs_rat (abs_frac (N, D)) with N D int
   numerals and D positive -- not by conditional computeLib rewriting:
   computeLib's CBV engine does not chain multi-hypothesis conditional
   rules reliably, so the decision procedures below run as ordinary ML
   conversions and are wired into the compset with
   [[computeLib.add_conv]], exactly as reduceLib wires numeral DIV/MOD.
   On an open term the underlying [[ratLib.RAT_CALC_CONV]] never fails
   (its terminal branch and [[safe_norm]]'s REFL fallback guarantee a
   result), so a conversion normalises as far as it can and may return a
   partially reduced, not fully decided, equation; genuine
   [[Feedback.failwith]] is reserved for a side condition that truly
   cannot be discharged, e.g. division by a zero candidate.  Either way
   nothing unsound follows: [[Refute_EvalCompute.sml]] maps any
   non-[[T]]/[[F]] result to [[IsStuck]]. *)
structure Refute_EvalRat :> Refute_EvalRat = struct

  val rat_ty = ratSyntax.rat_ty

  val abs_rat_c = Term.prim_mk_const {Thy = "rat", Name = "abs_rat"}
  val rat_cons_c = Term.prim_mk_const {Thy = "rat", Name = "rat_cons"}

  (* A candidate with denominator 1 prints as a bare rat_of_num numeral,
     negated with rat_ainv when negative; anything else prints as N // D
     via rat_cons.  Both shapes evaluate to abs_rat (abs_frac (n, d)), so
     a binding displays the way the user would have written it without
     needing a display postprocessor. *)
  fun mk_rat_lit (n, 1) = ratSyntax.term_of_int (Arbint.fromInt n)
    | mk_rat_lit (n, d) =
        Term.list_mk_comb
          (rat_cons_c,
           [intSyntax.term_of_int (Arbint.fromInt n),
            intSyntax.term_of_int (Arbint.fromInt d)])

  val frac_ss =
    simpLib.++ (intSimps.int_ss,
      simpLib.rewrites [fracTheory.NMR, fracTheory.DNM,
        intExtensionTheory.SGN_def])

  fun norm_conv tm = simpLib.SIMP_CONV frac_ss [] tm
  (* [TRY_CONV] turns a failure into [UNCHANGED], which [QCONV] then
     turns into the reflexive theorem: both recovery arms, spelled once. *)
  val safe_norm = Conv.QCONV (Conv.TRY_CONV norm_conv)

  fun discharge_prop h = Drule.EQT_ELIM (norm_conv h)

  (* [[discharge_prop]] is only ever built from [[frac_ss]] on a
     hypothesis-free side condition, so [[result]] should already come
     back clean; assert that instead of trusting it, so a future
     hypothesis-carrying [[discharge_prop]] result fails loudly here
     rather than propagating silently into a certified theorem. *)
  fun discharge_hyps thm =
    let
      val result =
        List.foldl (fn (h, th) => Drule.PROVE_HYP (discharge_prop h) th)
          thm (Thm.hyp thm)
    in
      if null (Thm.hyp result) then result
      else Feedback.failwith "discharge_hyps: residual hypotheses"
    end

  (* Reduce a :rat term towards abs_rat (abs_frac (N, D)) literal form.
     On an open or otherwise malformed term it normalises as far as it
     can and returns a partially reduced equation instead of failing;
     genuine failure is reserved for an undischargeable side condition,
     e.g. division by a zero candidate. *)
  fun RAT_DECIDE_CONV tm =
    (let
      val step1 = discharge_hyps (ratLib.RAT_CALC_CONV tm)
      val f = Term.rand (boolSyntax.rhs (Thm.concl step1))
      val step2 = discharge_hyps (fracLib.FRAC_CALC_CONV f)
      val combined = Thm.TRANS step1 (Thm.AP_TERM abs_rat_c step2)
      val norm = safe_norm (boolSyntax.rhs (Thm.concl combined))
    in
      Thm.TRANS combined norm
    end)
    handle Feedback.HOL_ERR _ => Feedback.failwith "RAT_DECIDE_CONV"
         | Conv.UNCHANGED => Feedback.failwith "RAT_DECIDE_CONV"

  (* Shared "decide both sides, cross-multiply via [[calc_thm]], then
     normalise" shape behind [[=]], [[<]] and [[<=]]; [[>]] and [[>=]]
     derive from the latter two instead of duplicating it a third and
     fourth time. *)
  fun RAT_CMP_STEP calc_thm head_tm (l, r) =
    let
      val lth = RAT_DECIDE_CONV l
      val rth = RAT_DECIDE_CONV r
      val f1 = Term.rand (boolSyntax.rhs (Thm.concl lth))
      val f2 = Term.rand (boolSyntax.rhs (Thm.concl rth))
      val cross = discharge_hyps (Drule.SPECL [f1, f2] calc_thm)
      val step1 = Thm.MK_COMB (Thm.AP_TERM head_tm lth, rth)
      val step2 = Thm.TRANS step1 cross
      val decided = safe_norm (boolSyntax.rhs (Thm.concl step2))
    in
      Thm.TRANS step2 decided
    end

  (* The redex type is checked before any work: this conversion sits on
     the polymorphic [[=]] key and is therefore offered every equality
     computeLib meets, at every type (see [[rat_eq_tm]] below).  Reaching
     [[RAT_CMP_STEP]] with, say, a datatype constructor on the left runs
     [[ratLib.RAT_CALC_CONV]] on it, which fails only after parsing --
     announcing an invented type variable per call, on the hot path of
     every compute-substrate candidate. *)
  fun RAT_EQ_DECIDE_CONV tm =
    (let
      val (l, r) = boolSyntax.dest_eq tm
    in
      if Refute_Util.same_type (Term.type_of l) rat_ty then
        RAT_CMP_STEP ratTheory.RAT_EQ (Term.rator (Term.rator tm)) (l, r)
      else Feedback.failwith "RAT_EQ_DECIDE_CONV"
    end)
    handle Feedback.HOL_ERR _ => Feedback.failwith "RAT_EQ_DECIDE_CONV"
         | Conv.UNCHANGED => Feedback.failwith "RAT_EQ_DECIDE_CONV"

  fun order_conv name calculate head dest tm =
    RAT_CMP_STEP calculate head (dest tm)
    handle Feedback.HOL_ERR _ => Feedback.failwith name
         | Conv.UNCHANGED => Feedback.failwith name

  val RAT_LES_DECIDE_CONV =
    order_conv "RAT_LES_DECIDE_CONV" ratTheory.RAT_LES_CALCULATE
      ratSyntax.rat_les_tm ratSyntax.dest_rat_les
  val RAT_LEQ_DECIDE_CONV =
    order_conv "RAT_LEQ_DECIDE_CONV" ratTheory.RAT_LEQ_CALCULATE
      ratSyntax.rat_leq_tm ratSyntax.dest_rat_leq

  (* [rat_gre_def] and [rat_geq_def] swap the arguments of [rat_les] and
     [rat_leq]; rewrite and reuse the conversions above. *)
  fun swapped_conv name definition decide tm =
    (let val step = Conv.REWR_CONV definition tm
     in Thm.TRANS step (decide (boolSyntax.rhs (Thm.concl step))) end)
    handle Feedback.HOL_ERR _ => Feedback.failwith name

  val RAT_GRE_DECIDE_CONV =
    swapped_conv "RAT_GRE_DECIDE_CONV" ratTheory.rat_gre_def
      RAT_LES_DECIDE_CONV
  val RAT_GEQ_DECIDE_CONV =
    swapped_conv "RAT_GEQ_DECIDE_CONV" ratTheory.rat_geq_def
      RAT_LEQ_DECIDE_CONV

  (* computeLib keys on (Name, Thy) alone, so [rat_eq_tm] shares the
     polymorphic [=] key and its conversion is offered equality redexes
     at every type; RAT_EQ_DECIDE_CONV's own type guard keeps it off
     them. *)
  val rat_eq_tm =
    Term.inst [{redex = Type.alpha, residue = rat_ty}] boolSyntax.equality

  (* Delete each arithmetic key's existing entry so the conversion added
     after it is the only one computeLib tries, re-inserting through
     [add_convs] because [del_consts] removed the keys; occurrences inside
     rules compiled earlier keep the old clauses.  [rat_eq_tm] must
     never be deleted: that would drop equality at every type.  Not
     idempotent (a second call appends a second equality conversion), so
     it runs once, from [register]. *)
  fun install () =
    let
      val () = computeLib.del_consts
        [ratSyntax.rat_add_tm, ratSyntax.rat_sub_tm, ratSyntax.rat_mul_tm,
         ratSyntax.rat_div_tm, ratSyntax.rat_ainv_tm, ratSyntax.rat_minv_tm,
         ratSyntax.rat_les_tm, ratSyntax.rat_leq_tm, ratSyntax.rat_gre_tm,
         ratSyntax.rat_geq_tm]
    in
      computeLib.add_convs
        [(ratSyntax.rat_add_tm, 2, RAT_DECIDE_CONV),
         (ratSyntax.rat_sub_tm, 2, RAT_DECIDE_CONV),
         (ratSyntax.rat_mul_tm, 2, RAT_DECIDE_CONV),
         (ratSyntax.rat_div_tm, 2, RAT_DECIDE_CONV),
         (ratSyntax.rat_ainv_tm, 1, RAT_DECIDE_CONV),
         (ratSyntax.rat_minv_tm, 1, RAT_DECIDE_CONV),
         (ratSyntax.rat_les_tm, 2, RAT_LES_DECIDE_CONV),
         (ratSyntax.rat_leq_tm, 2, RAT_LEQ_DECIDE_CONV),
         (ratSyntax.rat_gre_tm, 2, RAT_GRE_DECIDE_CONV),
         (ratSyntax.rat_geq_tm, 2, RAT_GEQ_DECIDE_CONV),
         (rat_eq_tm, 2, RAT_EQ_DECIDE_CONV)]
    end

  val generator : Refute_Gen.custom_gen =
    Refute_EvalCompute.fraction_generator mk_rat_lit

  fun register () =
    (install (); Refute_Gen.register_generator rat_ty generator)

end
