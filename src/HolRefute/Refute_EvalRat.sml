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
structure Refute_EvalRat :> sig
  val generator : Refute_Gen.custom_gen
  val register : unit -> unit
end = struct

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
  fun safe_norm tm = norm_conv tm handle Feedback.HOL_ERR _ => Thm.REFL tm
                                        | Conv.UNCHANGED => Thm.REFL tm

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

  fun RAT_EQ_DECIDE_CONV tm =
    RAT_CMP_STEP ratTheory.RAT_EQ (Term.rator (Term.rator tm))
      (boolSyntax.dest_eq tm)
    handle Feedback.HOL_ERR _ => Feedback.failwith "RAT_EQ_DECIDE_CONV"
         | Conv.UNCHANGED => Feedback.failwith "RAT_EQ_DECIDE_CONV"

  fun RAT_LES_DECIDE_CONV tm =
    RAT_CMP_STEP ratTheory.RAT_LES_CALCULATE ratSyntax.rat_les_tm
      (ratSyntax.dest_rat_les tm)
    handle Feedback.HOL_ERR _ => Feedback.failwith "RAT_LES_DECIDE_CONV"
         | Conv.UNCHANGED => Feedback.failwith "RAT_LES_DECIDE_CONV"

  fun RAT_LEQ_DECIDE_CONV tm =
    RAT_CMP_STEP ratTheory.RAT_LEQ_CALCULATE ratSyntax.rat_leq_tm
      (ratSyntax.dest_rat_leq tm)
    handle Feedback.HOL_ERR _ => Feedback.failwith "RAT_LEQ_DECIDE_CONV"
         | Conv.UNCHANGED => Feedback.failwith "RAT_LEQ_DECIDE_CONV"

  (* rat_gre_def and rat_geq_def are argument swaps of rat_les/rat_leq
     (ratScript.sml:233,235), so rewrite to the swapped form and hand
     off to the conversion already proven above, instead of repeating
     the cross-multiplication a third and fourth time. *)
  fun RAT_GRE_DECIDE_CONV tm =
    (let
      val step1 = Conv.REWR_CONV ratTheory.rat_gre_def tm
      val step2 = RAT_LES_DECIDE_CONV (boolSyntax.rhs (Thm.concl step1))
    in
      Thm.TRANS step1 step2
    end)
    handle Feedback.HOL_ERR _ => Feedback.failwith "RAT_GRE_DECIDE_CONV"

  fun RAT_GEQ_DECIDE_CONV tm =
    (let
      val step1 = Conv.REWR_CONV ratTheory.rat_geq_def tm
      val step2 = RAT_LEQ_DECIDE_CONV (boolSyntax.rhs (Thm.concl step1))
    in
      Thm.TRANS step1 step2
    end)
    handle Feedback.HOL_ERR _ => Feedback.failwith "RAT_GEQ_DECIDE_CONV"

  (* Equality at :rat is [[rat_eq_tm]], an instance of polymorphic [[=]]
     (min$=).  [[computeLib.add_extern]] keys solely on (Name, Thy), so
     ("=", "min") is one key shared by every type, and the [[Conv]]
     branch of [[reduce_cst]] (src/compute/src/equations.sml:175-185)
     never checks the redex's head constant against that key at all
     (unlike the [[Rewrite]] branch's [[match_term]] at :156): the conv
     below really is tried against equality redexes at any type that
     reach it.  It is safe for two reasons: [[add_convs]] appends it
     after whatever rules the key already has, so those win first, and
     it raises [[HOL_ERR]] on a non-rat redex, which [[reduce_cst]]
     catches and falls through on. *)
  val rat_eq_tm =
    Term.inst [{redex = Type.alpha, residue = rat_ty}] boolSyntax.equality

  (* rat_add, rat_sub and rat_mul have ordinary but empty compset
     entries from their Definition; rat_div has none at all; only
     rat_ainv, rat_minv and rat_les carry rules.  [[computeLib.del_consts]]
     removes whatever entry each key below already has so the conv
     registered immediately after is the only one computeLib can try;
     unlike [[scrub_const]], it threads the update through the
     persistent global compset ref, so the deletion actually takes
     effect for every redex compiled from here on.  It does not reach an
     occurrence sitting inside an already-compiled rule's right-hand
     side: [[from_term]] captures each constant's clause ref as the rule
     is added (src/compute/src/clauses.sml:311-314) while
     [[scrub_const]] deletes only the dictionary entry, so such an
     occurrence still sees the pre-deletion clauses.  Like the shared
     [[=]] key above, it keys on (Name, Thy)
     alone, so it must never run on [[rat_eq_tm]]: deleting that key
     would remove equality reduction for every type, not just rat. *)
  (* [[computeLib.add_conv]] on an existing key mutates that key's clause
     list in place, but [[del_consts]] just removed these keys, so the
     re-insertion below needs [[add_convs]]'s [[upd_compset]] threading,
     not a raw per-call [[add_conv]] whose return value is discarded. *)
  (* Runs once, from [[register]] below, at Refute's module load; not
     idempotent -- [[rat_eq_tm]] is correctly absent from [[del_consts]],
     so a second call would append a second [[RAT_EQ_DECIDE_CONV]] to
     the shared [[=]] chain rather than replacing the first. *)
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
