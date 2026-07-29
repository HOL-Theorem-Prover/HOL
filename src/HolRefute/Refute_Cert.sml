structure Refute_Cert = struct
  type term = Term.term

  datatype result =
      Certified of Refute_Core.counterexample
    | Potential of Refute_Core.counterexample
    | Discarded

  fun instantiate env tm =
    Term.subst (map (fn (variable, value) =>
      {redex = variable, residue = value}) env) tm

  val rhs_of = boolSyntax.rhs o Thm.concl

  fun conform_conclusion label expected theorem =
    Thm.EQ_MP (Thm.ALPHA (Thm.concl theorem) expected) theorem
    handle Feedback.HOL_ERR _ => raise Fail
      (label ^ " conclusion mismatch: " ^
       Parse.term_to_string (Thm.concl theorem) ^ " versus " ^
       Parse.term_to_string expected)

  fun eval tm = computeLib.CBV_CONV (!computeLib.the_compset) tm

  fun eval_original tm =
    if Refute_Core.has_bounded_quantifier tm then
      let
        val rewritten =
          Ho_Rewrite.REWRITE_CONV Refute_Core.bounded_rewrites tm
        val normalized = rhs_of rewritten
      in
        Thm.TRANS rewritten (eval normalized)
      end
    else
      eval tm

  fun head_name tm =
    let
      fun visit candidate =
        let val (head, arguments) = boolSyntax.strip_comb candidate
        in
          if boolSyntax.is_eq candidate orelse boolSyntax.is_neg candidate then
            (case arguments of
                argument :: _ => visit argument
              | [] => Parse.term_to_string candidate)
          else if Term.is_const head then Parse.term_to_string head
          else
            case arguments of
                argument :: _ => visit argument
              | [] => Parse.term_to_string candidate
        end
    in
      visit tm handle _ => Parse.term_to_string tm
    end

  fun eval_term env tm =
    (rhs_of (eval (instantiate env tm))
     handle Interrupt => raise Interrupt
          | _ => Term.mk_var ("?", Term.type_of tm))

  fun closure_of tm =
    let
      val (bound, body) = boolSyntax.strip_forall tm
      val free = Term.free_vars_lr body
      val variables = bound @ List.filter (fn variable =>
        not (List.exists (fn other => Term.aconv variable other) bound)) free
    in
      (variables, boolSyntax.list_mk_forall (variables, body), body)
    end

  fun replace (cex : Refute_Core.counterexample) certainty evals cert =
    { backend = #backend cex,
      substrate = #substrate cex,
      certainty = certainty,
      bindings = #bindings cex,
      evals = evals,
      cert = cert,
      scope = #scope cex,
      model = #model cex,
      stats = #stats cex }

  fun certify {original, evals, env, cex} =
    let
      val (variables, closure, body) = closure_of original
      val instance = instantiate env body
    in
      case (SOME (eval_original instance)
            handle Interrupt => raise Interrupt | _ => NONE) of
          NONE =>
            Potential (replace cex
              (Refute_Core.Potential
                ["evaluation stuck on: " ^ head_name instance]) [] NONE)
        | SOME theorem =>
            (case rhs_of theorem of
                rhs =>
                  if Term.aconv rhs boolSyntax.T then Discarded
                  else if not (Term.aconv rhs boolSyntax.F) then
                    Potential (replace cex
                      (Refute_Core.Potential
                        ["evaluation stuck on: " ^ head_name rhs]) [] NONE)
                  else
                    let
                      val negated_instance = Drule.EQF_ELIM theorem
                      val assumed = Thm.ASSUME closure
                      val witnesses = map (instantiate env) variables
                      val assumed_instance = Drule.SPECL witnesses assumed
                      val falsehood = Thm.MP (Thm.NOT_ELIM negated_instance)
                        assumed_instance
                      val certificate = Thm.NOT_INTRO
                        (Thm.DISCH closure falsehood)
                      val values = map (fn tm => (tm, eval_term env tm)) evals
                    in
                      Certified (replace cex Refute_Core.Genuine values
                        (SOME certificate))
                    end)
    end

  fun grounding_failure cex =
    Potential (replace cex
      (Refute_Core.Potential
        ["partial counterexample; grounding uncertifiable"]) [] NONE)

  (* Bindings in [cex] deliberately remain partial for display.  Native
     narrowing supplies a separately reconstructed environment grounded from
     the exact shapes used by that compile; no later generator lookup occurs. *)
  fun ground_and_certify {original, evals, env, ground_env, cex} =
    let
      val grounded =
        case ground_env of
            SOME values => values
          | NONE => raise Fail "narrowing grounding shape unavailable"
    in
      case certify
        {original = original, evals = evals, env = grounded, cex = cex} of
          result as Certified _ => result
        | Discarded => Discarded
        | _ => grounding_failure cex
    end
    handle Interrupt => raise Interrupt
         | _ => grounding_failure cex
end
