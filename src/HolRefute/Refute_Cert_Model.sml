structure Refute_Cert_Model = struct
  open Refute_Cert
  structure Util = Refute_Util

  datatype result =
      Certified of Thm.thm
    | NoCertificate of string
    | DiscardedByWholeFormulaEval

  exception ReplayFailure of string
  exception ResourceExhausted of string

  fun error_text error =
    let val message = General.exnMessage error
    in if message = "" then "unknown proof failure" else message end
    handle _ => "unknown proof failure"

  fun certify {original, env, hints, fuel, deadline} =
    let
      val remaining = ref (Int.max (0, fuel))

      fun check_resources operation =
        let
          val _ =
            case deadline of
                SOME limit =>
                  if Time.now () >= limit then
                    raise ResourceExhausted "replay deadline exhausted"
                  else ()
              | NONE => ()
        in
          if !remaining <= 0 then
            raise ResourceExhausted
              ("replay fuel exhausted before " ^ operation)
          else
            remaining := !remaining - 1
        end

      fun checked theorem =
        null (Thm.hyp theorem) andalso trusted theorem

      fun simplify tm =
        let
          val _ = check_resources "simplification"
          val theorem =
            simpLib.SIMP_CONV (BasicProvers.srw_ss ()) [] tm
            handle Conv.UNCHANGED => Thm.REFL tm
        in
          if checked theorem then SOME theorem else NONE
        end
        handle Interrupt => raise Interrupt
             | ResourceExhausted detail => raise ResourceExhausted detail
             | _ => NONE

      fun cbv tm =
        let
          val _ = check_resources "CBV evaluation"
          val theorem = eval_original tm
        in
          if checked theorem then SOME theorem else NONE
        end
        handle Interrupt => raise Interrupt
             | ResourceExhausted detail => raise ResourceExhausted detail
             | _ => NONE

      fun decisive theorem =
        let val rhs = rhs_of theorem
        in
          Term.aconv rhs boolSyntax.T orelse
          Term.aconv rhs boolSyntax.F
        end

      fun evaluate tm =
        let
          fun simplified () =
            case simplify tm of
                NONE => NONE
              | SOME theorem =>
                  let val reduced = rhs_of theorem
                  in
                    if decisive theorem then SOME theorem
                    else
                      case cbv reduced of
                          SOME evaluated =>
                            let val combined = Thm.TRANS theorem evaluated
                            in
                              if checked combined andalso decisive combined
                              then SOME combined
                              else NONE
                            end
                        | NONE => NONE
                  end
        in
          case cbv tm of
              SOME theorem =>
                if decisive theorem then SOME theorem else simplified ()
            | NONE => simplified ()
        end

      val (variables, closure, body) = closure_of original
      val expected = boolSyntax.mk_neg closure
      val instance = instantiate env body

      fun fast_certificate theorem =
        let
          val negated_instance = Drule.EQF_ELIM theorem
          val assumed = Thm.ASSUME closure
          val witnesses = map (instantiate env) variables
          val assumed_instance = Drule.SPECL witnesses assumed
          val falsehood = Thm.MP (Thm.NOT_ELIM negated_instance)
            assumed_instance
          val certificate = Thm.NOT_INTRO
            (Thm.DISCH closure falsehood)
          val certificate = conform_conclusion
            "whole-formula replay" expected certificate
        in
          if checked certificate then certificate
          else raise ReplayFailure
            "whole-formula certificate failed its trust checks"
        end

      val fast = evaluate instance
    in
      case fast of
          SOME theorem =>
            if Term.aconv (rhs_of theorem) boolSyntax.F then
              Certified (fast_certificate theorem)
            else if Term.aconv (rhs_of theorem) boolSyntax.T andalso
                    null (Term.free_vars_lr instance) then
              DiscardedByWholeFormulaEval
            else
              replay_pnf
                {original = original, closure = closure, expected = expected,
                 env = env, hints = hints,
                 check_resources = check_resources,
                 evaluate = evaluate, checked = checked}
        | NONE =>
            replay_pnf
              {original = original, closure = closure, expected = expected,
               env = env, hints = hints,
               check_resources = check_resources,
               evaluate = evaluate, checked = checked}
    end
    handle Interrupt => raise Interrupt
         | ResourceExhausted detail => NoCertificate detail
         | ReplayFailure detail => NoCertificate detail
         | error => NoCertificate (error_text error)

  and replay_pnf
        {original, closure, expected, env, hints,
         check_resources, evaluate, checked} =
    let
      val _ = check_resources "normalization"
      val normalized_equality =
        Ho_Rewrite.REWRITE_CONV Refute_Core.normal_rewrites closure
      val _ = if checked normalized_equality then () else
        raise ReplayFailure "normalization failed its trust checks"
      val normalized = rhs_of normalized_equality
      val _ = check_resources "prenex conversion"
      val prenex_equality = Refute_Narrow.prenex_conversion normalized
      val _ = if checked prenex_equality then () else
        raise ReplayFailure "prenex conversion failed its trust checks"
      val pnf = rhs_of prenex_equality

      fun strip tm =
        if boolSyntax.is_forall tm then
          strip (#2 (boolSyntax.dest_forall tm))
        else if boolSyntax.is_exists tm then
          strip (#2 (boolSyntax.dest_exists tm))
        else tm
      fun quantified tm =
        boolSyntax.is_forall tm orelse boolSyntax.is_exists tm
      val matrix = strip pnf
      val _ =
        if null (HolKernel.find_terms quantified matrix) then ()
        else raise ReplayFailure
          "normalization left a quantifier outside the prenex prefix"

      fun add_unique (candidate, accumulated) =
        if List.exists (fn old => Term.aconv old candidate) accumulated then
          accumulated
        else accumulated @ [candidate]
      val pool = List.foldl add_unique [] (map #2 env @ hints)
      val base_avoids = List.concat
        (map Term.all_vars (original :: map #1 env @ map #2 env @ hints))

      type failed_state =
        {formula : term,
         active_types : Type.hol_type list,
         candidates : term list}
      val failed = ref ([] : failed_state list)

      fun abstract active tm = Term.list_mk_abs (active, tm)
      fun same_types (left, right) =
        length left = length right andalso
        ListPair.allEq (fn (a, b) => Util.same_type a b) (left, right)
      fun same_terms (left, right) =
        length left = length right andalso
        ListPair.allEq (fn (a, b) => Term.aconv a b) (left, right)
      fun state active formula candidates : failed_state =
        {formula = abstract active formula,
         active_types = map Term.type_of active,
         candidates = map (abstract active) candidates}
      fun same_state (left : failed_state) (right : failed_state) =
        Term.aconv (#formula left) (#formula right) andalso
        same_types (#active_types left, #active_types right) andalso
        same_terms (#candidates left, #candidates right)
      fun seen current =
        List.exists (fn old => same_state old current) (!failed)
      fun remember current =
        if seen current then () else failed := current :: !failed

      fun applications target active base =
        let
          fun walk current [] = []
            | walk current (variable :: rest) =
                (case Lib.total Type.dom_rng (Term.type_of current) of
                     SOME (domain, _) =>
                       if Util.same_type domain (Term.type_of variable) then
                         let
                           val _ = check_resources
                             "candidate application generation"
                           val applied = Term.mk_comb (current, variable)
                           val here =
                             if Util.same_type target
                               (Term.type_of applied) then [applied]
                             else []
                         in
                           here @ walk applied rest @ walk current rest
                         end
                       else walk current rest
                   | NONE => [])
        in
          walk base active
        end

      fun candidates target active =
        let
          val direct = List.filter (fn candidate =>
            Util.same_type target (Term.type_of candidate)) pool
          val applied = List.concat (map (applications target active) pool)
        in
          List.foldl add_unique [] (direct @ applied)
        end

      fun prove_neg formula active =
        let
          val _ = check_resources "replay node"
        in
          if boolSyntax.is_forall formula then
            let
              val (variable, body) = boolSyntax.dest_forall formula
              val witnesses = candidates (Term.type_of variable) active
              val current = state active formula witnesses
              val _ = if seen current then
                  raise ReplayFailure "memoized replay failure"
                else ()

              fun attempt [] =
                    (remember current;
                     raise ReplayFailure
                       "no witness candidate refuted a universal prefix")
                | attempt (witness :: rest) =
                    let
                      val _ = check_resources "candidate branch"
                      val instance = Term.subst
                        [{redex = variable, residue = witness}] body
                      val refutation = prove_neg instance active
                      val assumed = Thm.ASSUME formula
                      val assumed_instance = Drule.SPECL [witness] assumed
                      val falsehood = Thm.MP (Thm.NOT_ELIM refutation)
                        assumed_instance
                      val theorem = Thm.NOT_INTRO
                        (Thm.DISCH formula falsehood)
                    in
                      if checked theorem then theorem
                      else raise ReplayFailure
                        "universal replay failed its trust checks"
                    end
                    handle Interrupt => raise Interrupt
                         | ResourceExhausted detail =>
                             raise ResourceExhausted detail
                         | _ => attempt rest
            in
              attempt witnesses
            end
          else if boolSyntax.is_exists formula then
            let
              val current = state active formula []
              val _ = if seen current then
                  raise ReplayFailure "memoized replay failure"
                else ()
              val (variable, body) = boolSyntax.dest_exists formula
              val avoids = base_avoids @ active @ Term.all_vars formula
              val arbitrary = Term.variant avoids variable
              val instance = Term.subst
                [{redex = variable, residue = arbitrary}] body
              val refutation =
                (prove_neg instance (active @ [arbitrary])
                 handle ReplayFailure detail =>
                   (remember current; raise ReplayFailure detail))
              val generalized = Thm.GEN arbitrary refutation
              val conversion = Conv.CONV_RULE
                (Conv.DEPTH_CONV Thm.BETA_CONV)
                (Drule.ISPEC (Term.mk_abs (variable, body))
                  boolTheory.NOT_EXISTS_THM)
              val target = rhs_of conversion
              val generalized = conform_conclusion
                "existential replay" target generalized
              val theorem = Thm.EQ_MP (Thm.SYM conversion) generalized
            in
              if checked theorem then theorem
              else raise ReplayFailure
                "existential replay failed its trust checks"
            end
          else
            let
              val current = state active formula []
              val _ = if seen current then
                  raise ReplayFailure "memoized replay failure"
                else ()
            in
              case evaluate formula of
                  SOME theorem =>
                    if Term.aconv (rhs_of theorem) boolSyntax.F then
                      Drule.EQF_ELIM theorem
                    else
                      (remember current;
                       raise ReplayFailure
                         "replay leaf did not normalize to false")
                | NONE =>
                    (remember current;
                     raise ReplayFailure
                       "replay leaf could not be normalized")
            end
        end

      val replayed = prove_neg pnf []
      val prenex_negated_equality =
        Thm.AP_TERM boolSyntax.negation prenex_equality
      val replayed = conform_conclusion
        "prenex replay" (rhs_of prenex_negated_equality) replayed
      val normalized_certificate =
        Thm.EQ_MP (Thm.SYM prenex_negated_equality) replayed
      val normalized_negated_equality =
        Thm.AP_TERM boolSyntax.negation normalized_equality
      val certificate = Thm.EQ_MP
        (Thm.SYM normalized_negated_equality) normalized_certificate
      val certificate = conform_conclusion
        "model replay" expected certificate
    in
      if checked certificate then Certified certificate
      else NoCertificate "replay certificate failed its final trust checks"
    end
end
