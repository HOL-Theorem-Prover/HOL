(* Quickcheck generator and compset fragment for :real.

   Unlike :rat, :real's arithmetic and comparison operators already
   decide on numeral (rational-literal) redexes: realSimps.sml installs
   an [[elim_common_factor]] conv for [[/]] plus a family of literal
   rewrites into the global compset the moment realLib loads, and
   Refute_Cert_Model.sml's genuine dependency on [[realLib.REAL_ARITH]]
   forces that load whenever Refute is used.  This fragment adds exactly
   one thing that gap leaves open -- [[inv]], which has no compset entry
   of its own -- and otherwise only supplies the generator.

   The decided form is [[real_of_num n]] (or its [[real_neg]]) for a
   whole number, else [[real_div]] of such a numerator over a positive
   [[real_of_num]] denominator: this is the same shape [[elim_common_factor]]
   already produces, so a candidate or an [[inv]] result never needs a
   second, incompatible normal form.

   [[inv]]'s decision is derived, not discovered: [[REAL_INV_DIV']] gives
   the unconditional swap [[inv (x / y) = y * inv x]], which -- since
   [[y * inv x]] is definitionally [[y / x]] -- yields [[inv (x/y) = y/x]]
   for every real [[x]] and [[y]], including the junk-value cases
   [[x = 0]] and [[y = 0]].  Applying that swap to a canonical numerator
   over a positive denominator can turn a positive denominator negative
   (e.g. inv (-3/4) swaps to 4/(-3)), so a second unconditional identity,
   [[p/q = -p/-q]], restores the positive-denominator convention before
   the result is handed back.  Zero is refused before any of this runs:
   [[inv 0 = 0]] is a theorem, so reducing it would not be unsound, but
   [[x / 0]] already declines rather than reducing, and matching that
   existing convention beats introducing a second one. *)
structure Refute_EvalReal :> sig
  val generator : Refute_Gen.custom_gen
  val register : unit -> unit
end = struct

  val real_ty = realSyntax.real_ty

  (* A candidate with denominator 1 prints as a bare (possibly negated)
     numeral; anything else prints as [[N / D]] via real division, the
     same shape the compset itself decides to, so a binding displays the
     way the user would have written it. *)
  fun mk_real_lit (n, 1) = realSyntax.term_of_int (Arbint.fromInt n)
    | mk_real_lit (n, d) =
        realSyntax.mk_div
          (realSyntax.term_of_int (Arbint.fromInt n),
           realSyntax.term_of_int (Arbint.fromInt d))

  val x_var = Term.mk_var ("x", real_ty)
  val y_var = Term.mk_var ("y", real_ty)

  (* [[inv (x/y) = y/x]] unconditionally: [[REAL_INV_DIV']] gives
     [[inv (x/y) = y * inv x]], and [[y * inv x]] is definitionally
     [[y/x]] ([[real_div]]'s own equation), including at x = 0 or
     y = 0. *)
  val swap_thm =
    let
      val step_a = Drule.SPECL [x_var, y_var] realTheory.REAL_INV_DIV'
      val step_b = Conv.GSYM (Drule.SPECL [y_var, x_var] realTheory.real_div)
    in
      Thm.GENL [x_var, y_var] (Thm.TRANS step_a step_b)
    end

  val p_var = Term.mk_var ("p", real_ty)
  val q_var = Term.mk_var ("q", real_ty)
  val negp = realSyntax.mk_negated p_var
  val negq = realSyntax.mk_negated q_var

  (* [[p/q = -p/-q]] unconditionally, via [[REAL_INV_NEG]] and
     [[REAL_NEG_MUL2]]: used to move a negative denominator produced by
     [[swap_thm]] back onto the numerator. *)
  val flip_thm =
    let
      val step1 = Drule.SPECL [p_var, q_var] realTheory.real_div
      val step2 = Drule.SPECL [negp, negq] realTheory.real_div
      val invneg_q = Thm.SPEC q_var realTheory.REAL_INV_NEG
      val step3 =
        Thm.AP_TERM (Term.mk_comb (realSyntax.mult_tm, negp)) invneg_q
      val step4 =
        Drule.SPECL [p_var, realSyntax.mk_inv q_var] realTheory.REAL_NEG_MUL2
      val rhs_chain = Thm.TRANS (Thm.TRANS step2 step3) step4
    in
      Thm.GENL [p_var, q_var] (Thm.TRANS step1 (Conv.GSYM rhs_chain))
    end

  val n_var = Term.mk_var ("n", numSyntax.num)
  val d_var = Term.mk_var ("d", numSyntax.num)
  val nR = realSyntax.mk_injected n_var
  val dR = realSyntax.mk_injected d_var

  val pos_frac_thm = Thm.GENL [n_var, d_var] (Drule.SPECL [nR, dR] swap_thm)

  (* [[swap_thm]] gives [[inv ((-&n)/&d) = &d/(-&n)]]; [[flip_thm]] moves
     the negation from denominator to numerator, leaving a double
     negation on the denominator that [[REAL_NEGNEG]] collapses. *)
  val neg_frac_thm =
    let
      val negnR = realSyntax.mk_negated nR
      val step1 = Drule.SPECL [negnR, dR] swap_thm
      val step2 = Drule.SPECL [dR, negnR] flip_thm
      val step3 = Conv.RAND_CONV (Conv.REWR_CONV realTheory.REAL_NEGNEG)
        (boolSyntax.rhs (Thm.concl step2))
    in
      Thm.GENL [n_var, d_var]
        (Thm.TRANS (Thm.TRANS step1 step2) step3)
    end

  (* [[a_term]] decided as [[+-&nn]]; raises on anything else (an open
     term, or a denominator not already in that shape), so an
     unparseable argument declines rather than mis-decides. *)
  fun magnitude_and_sign a_term =
    case Lib.total realSyntax.dest_negated a_term of
      SOME inner => (true, realSyntax.dest_injected inner)
    | NONE => (false, realSyntax.dest_injected a_term)

  (* Decide [[inv x]] where [[x]] has already been reduced to the
     compset's own canonical numeral-or-fraction shape.  Declines (via
     [[Feedback.failwith]]) on an open [[x]], on a non-positive
     denominator (never produced by that canonical shape, checked
     defensively), and on [[x = 0]] -- matching [[/]]'s existing refusal
     to reduce a zero divisor instead of introducing a second
     convention. *)
  fun REAL_INV_DECIDE_CONV tm =
    (let
      val t = realSyntax.dest_inv tm
      val (a_term, b_term) =
        if realSyntax.is_div t then realSyntax.dest_div t
        else (t, realSyntax.term_of_int Arbint.one)
      val (neg_a, nn) = magnitude_and_sign a_term
      val (neg_b, dd) = magnitude_and_sign b_term
      val _ = if neg_b then Feedback.failwith "negative denominator"
              else ()
      val _ = if numSyntax.dest_numeral nn = Arbnum.zero
              then Feedback.failwith "zero argument" else ()
      val _ = if numSyntax.dest_numeral dd = Arbnum.zero
              then Feedback.failwith "zero denominator" else ()
      val wrap_eq =
        if realSyntax.is_div t then Thm.REFL t
        else Conv.GSYM (Thm.SPEC t realTheory.REAL_OVER1)
      val step1 = Thm.AP_TERM realSyntax.inv_tm wrap_eq
      val base =
        Drule.SPECL [nn, dd] (if neg_a then neg_frac_thm else pos_frac_thm)
      val combined = Thm.TRANS step1 base
      val rhs = boolSyntax.rhs (Thm.concl combined)
      (* Collapse a denominator of 1 to a bare numeral, matching
         [[mk_real_lit]]'s own convention; [[REWR_CONV]] fails (rather
         than matching) when no such denominator is present. *)
      val collapsed =
        Conv.REWR_CONV realTheory.REAL_OVER1 rhs
        handle Feedback.HOL_ERR _ => Thm.REFL rhs
    in
      Thm.TRANS combined collapsed
    end)
    handle Feedback.HOL_ERR _ => Feedback.failwith "REAL_INV_DECIDE_CONV"

  (* [[inv]] has no compset entry of its own (real_inv's defining
     equation is [[nocompute]]), so this only adds; nothing is deleted
     or overridden, and no existing real rewrite is touched. *)
  fun install () =
    computeLib.add_convs [(realSyntax.inv_tm, 1, REAL_INV_DECIDE_CONV)]

  (* Numerators span [-size, size], the house GenNum Int convention
     (Refute_EvalCompute.sml). *)
  fun draw_numerator size state =
    let
      val radius = IntInf.fromInt (Int.max (0, size))
      val bound = 2 * radius + 1
      val (value, next) = Refute_Eval.checked_rand_below bound state
    in
      (IntInf.toInt value - IntInf.toInt radius, next)
    end

  (* Denominators are drawn as k + 1 for k in [0, size], so every
     candidate is well-formed by construction: no draw can reach a zero
     or negative denominator. *)
  fun draw_denominator size state =
    let
      val bound = IntInf.fromInt (Int.max (0, size) + 1)
      val (value, next) = Refute_Eval.checked_rand_below bound state
    in
      (IntInf.toInt value + 1, next)
    end

  fun random size state =
    let
      val (n, s1) = draw_numerator size state
      val (d, s2) = draw_denominator size s1
    in
      (mk_real_lit (n, d), s2)
    end

  fun gcd (a, 0) = a
    | gcd (a, b) = gcd (b, a mod b)

  fun in_lowest_terms (0, d) = (d = 1)
    | in_lowest_terms (n, d) = gcd (Int.abs n, d) = 1

  (* Restricted to lowest terms (0 admitted only as 0/1): every distinct
     rational at this radius is covered exactly once instead of via
     every non-reduced fraction that also fits, which only changes
     ordering, pinned nowhere. *)
  fun enumerate size =
    let val radius = Int.max (0, size)
    in
      List.concat
        (List.tabulate (radius + 1, fn k =>
          let val d = k + 1
          in
            List.mapPartial
              (fn i =>
                 let val n = i - radius
                 in
                   if in_lowest_terms (n, d) then SOME (mk_real_lit (n, d))
                   else NONE
                 end)
              (List.tabulate (2 * radius + 1, fn i => i))
          end))
    end

  val generator : Refute_Gen.custom_gen =
    { enumerate = SOME enumerate, random = SOME random }

  fun register () =
    (install (); Refute_Gen.register_generator real_ty generator)

end
