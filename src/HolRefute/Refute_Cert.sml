structure Refute_Cert = struct
  type term = Term.term

  datatype result =
      Certified of Refute_Core.counterexample
    | Uncertified of Refute_Core.counterexample
    | Potential of Refute_Core.counterexample
    | Discarded

  fun instantiate env tm =
    Term.subst (map (fn (variable, value) =>
      {redex = variable, residue = value}) env) tm

  val rhs_of = boolSyntax.rhs o Thm.concl

  val default_leaf_rounds = 2

  datatype instance_verdict =
      InstanceFalse of Thm.thm
    | InstanceTrue
    | InstanceStuck of string

  (* Shared by the narrowing and model replay engines: an exception raised
     inside a replay step is reported by message, never propagated. *)
  fun replay_error_text error =
    let val message = General.exnMessage error
    in if message = "" then "unknown proof failure" else message end
    handle Interrupt => raise Interrupt | _ => "unknown proof failure"

  (* Disk theorems are checked kernel imports: DISK_THM is the marker HOL4
     itself accepts, subtracting it in Theory.oracle_string_of and listing
     it in Sanity.accepted_oracles.  Every other oracle, and every axiom
     introduced in this session, crosses Refute's certification trust
     boundary.  Requiring an empty tag instead would reject every
     certificate whose evaluation touched a library rewrite, which is all
     of them. *)
  fun trusted theorem =
    Tag.isEmpty (Thm.tag theorem) orelse Tag.isDisk (Thm.tag theorem)

  fun conform_conclusion label expected theorem =
    Thm.EQ_MP (Thm.ALPHA (Thm.concl theorem) expected) theorem
    handle Feedback.HOL_ERR _ => raise Fail
      (label ^ " conclusion mismatch: " ^
       Parse.term_to_string (Thm.concl theorem) ^ " versus " ^
       Parse.term_to_string expected)

  fun eval tm = computeLib.CBV_CONV (computeLib.the_compset ()) tm

  (* [has_bounded_quantifier] is a syntactic over-approximation of what
     [bounded_rewrites] can rewrite; when the two disagree, [REWRITE_CONV]
     raises [UNCHANGED].  Catching that keeps a recogniser miss a lost
     speedup rather than a lost evaluation step: falling through to plain
     [eval] still decides the instance, just without the bounded shortcut. *)
  fun eval_original tm =
    if Refute_Core.has_bounded_quantifier tm then
      case Lib.total
        (Ho_Rewrite.REWRITE_CONV Refute_Core.bounded_rewrites) tm of
          SOME rewritten => Thm.TRANS rewritten (eval (rhs_of rewritten))
        | NONE => eval tm
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
      visit tm
      handle Interrupt => raise Interrupt | _ => Parse.term_to_string tm
    end

  (* A bounded, theorem-producing evaluator shared by QC certification and
     model replay.  [step] supplies the caller's exception, resource,
     deadline, and per-conversion audit policy. *)
  fun equality_portfolio rounds step tm =
    let
      fun acceptable theorem =
        null (Thm.hyp theorem) andalso trusted theorem andalso
        let val (left, _) = boolSyntax.dest_eq (Thm.concl theorem)
        in Term.aconv left tm end
        handle Feedback.HOL_ERR _ => false

      fun decisive theorem =
        let val rhs = rhs_of theorem
        in
          Term.aconv rhs boolSyntax.T orelse
          Term.aconv rhs boolSyntax.F
        end

      val seen = ref ([] : term list)
      fun repeated candidate = Refute_Util.aconv_member candidate (!seen)
      fun one label conversion theorem =
        case step label (rhs_of theorem) conversion of
            NONE => theorem
          | SOME next =>
              if Term.aconv (rhs_of next) (rhs_of theorem) then theorem
              else Thm.TRANS theorem next
      fun advance label conversion theorem =
        if decisive theorem then theorem
        else one label conversion theorem
      fun round 0 theorem = theorem
        | round count theorem =
            let
              val current = rhs_of theorem
              val _ = seen := current :: !seen
              val theorem = advance "leaf CBV evaluation" eval_original
                theorem
              val theorem = advance "leaf simplification"
                (simpLib.SIMP_CONV (BasicProvers.srw_ss ()) []) theorem
              val theorem = advance "leaf CBV evaluation" eval_original
                theorem
              val next = rhs_of theorem
            in
              if decisive theorem orelse Term.aconv current next orelse
                 repeated next then theorem
              else round (count - 1) theorem
            end
      val initial =
        case step "leaf beta/let normalization" tm
          (Conv.DEPTH_CONV Thm.BETA_CONV) of
            SOME theorem => theorem
          | NONE => Thm.REFL tm
      val theorem = round rounds initial
    in
      if acceptable theorem then SOME theorem else NONE
    end

  (* The [step] policy of the direct QC replays: a failing conversion is
     reported as [NONE]. *)
  fun plain_step _ input conversion =
    SOME (conversion input)
    handle Interrupt => raise Interrupt | _ => NONE

  fun is_quantifier tm =
    boolSyntax.is_forall tm orelse boolSyntax.is_exists tm

  fun evaluate_instance rounds step instance =
    case equality_portfolio rounds step instance of
        NONE => InstanceStuck (head_name instance)
      | SOME theorem =>
          let val rhs = rhs_of theorem
          in
            if Term.aconv rhs boolSyntax.F then InstanceFalse theorem
            else if Term.aconv rhs boolSyntax.T then InstanceTrue
            else InstanceStuck (head_name rhs)
          end

  fun eval_term env tm =
    ((let
        val input = instantiate env tm
        val theorem = eval input
        val result = rhs_of theorem
      in
        (* An open input can still have a closed, fully determined value.
           This matters for a reconstructed function update whose unknown
           fallback is not inspected at the evaluated point.  The trusted
           equality proves that the result is independent of every free
           fragment left on its input side. *)
        if null (Term.free_vars result) andalso null (Thm.hyp theorem) andalso
           trusted theorem then rhs_of theorem
        else Term.mk_var ("?", Term.type_of tm)
      end)
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

  (* Turn a refutation of one instance into a refutation of the universally
     quantified formula whose prefix [witnesses] instantiate. *)
  fun refute_forall formula witnesses refutation =
    let
      val assumed = Thm.ASSUME formula
      val assumed_instance = Drule.SPECL witnesses assumed
      val falsehood = Thm.MP (Thm.NOT_ELIM refutation) assumed_instance
    in
      Thm.NOT_INTRO (Thm.DISCH formula falsehood)
    end

  (* Turn a generalized refutation of [body] into a refutation of the
     corresponding existential formula. *)
  fun refute_exists label variable body generalized =
    let
      val conversion = Conv.CONV_RULE
        (Conv.DEPTH_CONV Thm.BETA_CONV)
        (Drule.ISPEC (Term.mk_abs (variable, body))
          boolTheory.NOT_EXISTS_THM)
      val target = rhs_of conversion
      val generalized = conform_conclusion label target generalized
    in
      Thm.EQ_MP (Thm.SYM conversion) generalized
    end

  (* Keep the derivation shared while letting each caller retain its own
     exception, budget, deadline, and audit policy for individual steps. *)
  fun normalize_to_pnf step closure =
    let
      val normalized_equality = step
        (Ho_Rewrite.REWRITE_CONV Refute_Core.normal_rewrites) closure
      val normalized = rhs_of normalized_equality
      val prenex_equality = step Refute_Narrow.prenex_conversion normalized
    in
      (normalized_equality, prenex_equality, rhs_of prenex_equality)
    end

  (* Undo the two equalities produced by [normalize_to_pnf] under negation. *)
  fun undo_normalization label
        (normalized_equality, prenex_equality) replayed =
    let
      val prenex_negated_equality =
        Thm.AP_TERM boolSyntax.negation prenex_equality
      val replayed = conform_conclusion
        (label ^ " prenex") (rhs_of prenex_negated_equality) replayed
      val normalized_certificate = Thm.EQ_MP
        (Thm.SYM prenex_negated_equality) replayed
      val normalized_negated_equality =
        Thm.AP_TERM boolSyntax.negation normalized_equality
    in
      Thm.EQ_MP (Thm.SYM normalized_negated_equality)
        normalized_certificate
    end

  (* One memoized TypeBase lookup belongs to each replay call: the theory
     cannot change underneath it. *)
  fun constructor_resolver () =
    let
      val cache = ref
        (Redblackmap.mkDict Type.compare :
          (Type.hol_type, term list option) Redblackmap.dict)
      fun resolve ty =
        case Redblackmap.peek (!cache, ty) of
            SOME constructors => constructors
          | NONE =>
              let
                val constructors =
                  Option.map (fn info => map (TypeBasePure.cinst ty)
                    (TypeBasePure.constructors_of info))
                    (TypeBase.fetch ty)
                  handle Feedback.HOL_ERR _ => NONE
                val _ = cache :=
                  Redblackmap.insert (!cache, ty, constructors)
              in
                constructors
              end
    in
      resolve
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

  fun uncertified cex =
    Uncertified (replace cex Refute_Core.Genuine [] NONE)

  (* Both certification paths must end at exactly the negated closure the
     caller supplied.  Keep theorem trust and display-evaluation attachment
     in one place so the PNF fallback cannot acquire a weaker audit than the
     direct whole-formula path. *)
  fun finish_certificate label closure evals env cex certificate =
    let
      val expected = boolSyntax.mk_neg closure
      val certificate = conform_conclusion label expected certificate
    in
      if null (Thm.hyp certificate) andalso trusted certificate then
        let val values = map (fn tm => (tm, eval_term env tm)) evals
        in
          Certified (replace cex Refute_Core.Genuine values
            (SOME certificate))
        end
      else
        uncertified cex
    end
    handle Interrupt => raise Interrupt | _ => uncertified cex

  (* Direct evaluation may be stuck on the quantified source even though
     theorem-producing normalization exposes the fully instantiated matrix
     that the QC backend tested.  Replay only an all-universal PNF prefix:
     environment values are specializations, never assumptions or evidence
     that an existential domain was exhausted. *)
  fun certify_universal_pnf {closure, evals, env, cex} =
    let
      fun normalization_step conversion tm = conversion tm
      val (normalized_equality, prenex_equality, pnf) =
        normalize_to_pnf normalization_step closure
      val (prefix, matrix) = Refute_Narrow.strip_quantifiers pnf
      val _ =
        if List.all (fn (Refute_Eval.Forall, _) => true | _ => false)
             prefix then ()
        else raise Fail "non-universal PNF prefix"
      val _ =
        if Lib.can (HolKernel.find_term is_quantifier) matrix then
          raise Fail "quantifier remains outside the PNF prefix"
        else ()

      fun binding_for (_, variable) =
        case List.filter (fn (key, _) => Term.aconv key variable) env of
            [(_, value)] =>
              if Refute_Util.same_type (Term.type_of value)
                   (Term.type_of variable) then
                (variable, value)
              else raise Fail "PNF binding has the wrong type"
          | _ => raise Fail "PNF binding is missing or duplicated"
      val bindings = map binding_for prefix
      val witnesses = map #2 bindings
      val instance = instantiate bindings matrix
      val _ = if null (Term.free_vars_lr instance) then ()
        else raise Fail "PNF matrix remains open"
    in
      case evaluate_instance default_leaf_rounds plain_step instance of
          InstanceFalse theorem =>
            let
              val negated_instance = Drule.EQF_ELIM theorem
              val replayed = refute_forall pnf witnesses negated_instance
              val certificate = undo_normalization "universal PNF replay"
                (normalized_equality, prenex_equality) replayed
            in
              finish_certificate "universal PNF replay" closure evals env cex
                certificate
            end
        | InstanceTrue => Discarded
        | InstanceStuck _ => uncertified cex
    end
    handle Interrupt => raise Interrupt | _ => uncertified cex

  fun certify {original, evals, env, cex} =
    let
      val (variables, closure, body) = closure_of original
      val instance = instantiate env body
    in
      case evaluate_instance default_leaf_rounds plain_step instance of
          InstanceStuck _ =>
            certify_universal_pnf
              {closure = closure, evals = evals, env = env, cex = cex}
        | InstanceTrue => Discarded
        | InstanceFalse theorem =>
            let
              val negated_instance = Drule.EQF_ELIM theorem
              val witnesses = map (instantiate env) variables
              val certificate = refute_forall closure witnesses
                negated_instance
            in
              finish_certificate "whole-formula replay" closure evals env cex
                certificate
            end
    end
    handle Interrupt => raise Interrupt | _ => uncertified cex

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
