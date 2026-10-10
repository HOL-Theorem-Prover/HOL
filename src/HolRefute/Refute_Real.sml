(* Optional real Quickcheck, model display and arithmetic replay support. *)
structure Refute_Real :> Refute_Real = struct
  local open Refute in end
  structure MFH = Refute_ModelFinder_HOL
  structure MFN = Refute_ModelFinder_Names
  structure Util = Refute_ModelFinder_Util
  val dest_frac_atom = Refute_ModelFinder_Model.dest_frac_atom

  (* [[real_of_num]] is [[nocompute]] -- it carries no compset entry of
     its own, unlike [[rat_of_num]], which unfolds via a genuine (if
     unused in practice) SUC-recursive definition -- yet a ground real
     numeral or [[n / d]] fraction built from it is exactly as much a
     closed, already-decided value as a NUMERAL literal: realSimps'
     rules pattern-match through [[real_of_num]]/[[real_neg]]/[[real_div]]
     directly, never by unfolding [[real_of_num]] itself.  Recognise that
     shape the same way [[Literal.is_literal]] recognises a bare numeral,
     so it is never mistaken for a stuck, non-executable constant.

     A fraction of two real literals is only ever actually decided by
     the compset when the numerator is zero (unconditional, by
     [[REAL_DIV_LZERO]]) or the denominator is a nonzero literal
     (negative denominators are first renormalised by [[realSimps]]'
     [[div_rats]]/[[div_ratls]]/[[div_ratrs]], positive ones handled
     directly): this is exactly [[realSimps.elim_common_factor]]'s own
     acceptance condition, which raises on a nonzero numerator over a
     zero denominator and so leaves it stuck.  Match that condition
     here so a term like [[1 / 0]] is not mistaken for a decided value. *)
  fun is_real_literal_fraction tm =
    realSyntax.is_div tm andalso
    let val (num, den) = realSyntax.dest_div tm in
      realSyntax.is_real_literal num andalso realSyntax.is_real_literal den
    end

  fun is_real_numeral_value tm =
    realSyntax.is_real_literal tm orelse
    (is_real_literal_fraction tm andalso
     let val (num, den) = realSyntax.dest_div tm in
       realSyntax.int_of_term num = Arbint.zero orelse
       realSyntax.int_of_term den <> Arbint.zero
     end)

  fun literal_constants tm =
    if is_real_numeral_value tm then SOME []
    else if is_real_literal_fraction tm then
      SOME [realSyntax.real_injection]
    else NONE

  (* [realLib.REAL_ARITH] is a prover ([term -> thm]), not a [conv]; the
     other two leaf decision procedures are already [conv]s, so wrap it
     the same way as [Drule.EQT_INTRO]. *)
  fun real_arith_conv goal = Drule.EQT_INTRO (realLib.REAL_ARITH goal)

  (* [REAL_ARITH] is two provers (the second Positivstellensatz-based)
     behind one flat fuel charge, so [decision_leaf] must not spend it
     on goals with no [:real] subterm at all - unlike
     [TAUT_CONV]/[OMEGA_CONV], it cannot even apply. *)
  fun mentions_real goal =
    Lib.can (HolKernel.find_term
      (fn tm => Util.same_type (Term.type_of tm) realSyntax.real_ty)) goal

  (* [realax$real] has no literal constructor the way [rat$rat_cons] does, so
     a reconstructed [abs_frac] value is rendered through division instead: a
     zero numerator or a denominator of [1] prints as the bare numerator
     (a real model value must print as [3], never [3 / 1]), any other
     denominator prints as [realSyntax.mk_div] of the two rendered integers.
     Rational display always prints [n // d]. *)
  fun frac_atom_to_real term =
    case dest_frac_atom term of
        NONE => term
      | SOME (numerator, denominator) =>
          (let
             val numerator_int = intSyntax.int_of_term numerator
             val denominator_int = intSyntax.int_of_term denominator
             val numerator_term = realSyntax.term_of_int numerator_int
           in
             if Arbint.compare (numerator_int, Arbint.zero) = EQUAL orelse
                Arbint.compare (denominator_int, Arbint.one) = EQUAL
             then numerator_term
             else
               realSyntax.mk_div
                 (numerator_term, realSyntax.term_of_int denominator_int)
           end handle Feedback.HOL_ERR _ => term)

  (* Narrowed to [:real] by type, not by the reserved name alone: [abs_frac]
     is [int # int -> frac] (retypes to neither [real] nor [rat]), so [rat]
     hits the identical opaque-reserved-variable fallback and a bare name
     match would also authorize it.  [MFN.original_name] alone is not
     enough either: it strips every generated-name layer, so a selector or
     discriminator wrapping the same tail ([refute$sel0$frac$abs_frac])
     would match too, hence the explicit [not (MFN.is_sel name)].  This
     predicate need not discriminate precisely for soundness - see
     [Refute_ModelFinder_Model.certification_env_with_holes]: a qualifying
     binding is dropped, not trusted. *)
  fun qualifying_frac_head head =
    case Lib.total Term.dest_var head of
        SOME (name, _) =>
          MFN.is_reserved_name name andalso not (MFN.is_sel name) andalso
          MFN.original_name name = "frac$abs_frac"
      | NONE => false

  fun qualifying_frac_binding (variable, value) =
    Util.same_type (Term.type_of variable) realSyntax.real_ty andalso
    Util.same_type (Term.type_of value) realSyntax.real_ty andalso
    (case HolKernel.strip_comb value of
         (head, [pair]) =>
           qualifying_frac_head head andalso
           (case Lib.total pairSyntax.dest_pair pair of
                SOME (n, d) =>
                  intSyntax.is_int_literal n andalso
                  intSyntax.is_int_literal d andalso
                  let val converted = frac_atom_to_real value in
                    not (Term.aconv converted value) andalso
                    null (Term.free_vars converted)
                  end
              | NONE => false)
       | _ => false)

  fun recover_frac_binding (binding as (_, value)) =
    if qualifying_frac_binding binding then SOME (frac_atom_to_real value)
    else NONE

  fun register () =
    (Refute_ModelFinder_Model.register_frac_type_with_display
       (MFH.real_frac_registration, realSyntax.real_ty, frac_atom_to_real);
     Refute_ModelFinder_Model.register_frac_replay recover_frac_binding;
     Refute_Core.register_literal_constants literal_constants;
     Refute_Cert_Model.register_real_arithmetic
       {applies = mentions_real, conv = real_arith_conv,
        tactic = realLib.REAL_ASM_ARITH_TAC};
     Refute_EvalReal.register ())

  val () = register ()
end
