structure Refute_Cert_Narrow = struct
  open Refute_Cert
  structure Util = Refute_Util

  fun replay_failure cex detail =
    Potential (replace cex
      (Refute_Core.Potential
        ["existential narrowing case-tree replay failed: " ^ detail])
      [] NONE)

  fun replay_error_text error =
    let val message = General.exnMessage error
    in if message = "" then "unknown proof failure" else message end
    handle _ => "unknown proof failure"

  (* Replay never infers exhaustiveness from a successful simplification.
     Every existential node's frozen shape and pattern cover are checked
     exactly.  Universal nodes need only one well-typed witness, so their
     possibly incomplete search shape is irrelevant to the proof.  Only an
     acyclic TypeBase constructor tree can support an exhaustive cover, so
     numeric prefixes, recursive truncations, and custom enumerations fail
     closed at existential nodes. *)
  fun certify_case_tree
        {original, evals, env, run_depth, case_tree, cex} =
    let
      val _ = if run_depth >= 0 then ()
        else raise Fail "negative narrowing run depth"
      val (_, closure, _) = closure_of original
      val prenex_equality = Refute_Narrow.prenex_conversion closure
      val pnf = rhs_of prenex_equality

      val constructor_cache =
        ref (Redblackmap.mkDict Type.compare :
          (Type.hol_type, term list) Redblackmap.dict)
      fun constructors_of ty =
        case Redblackmap.peek (!constructor_cache, ty) of
            SOME constructors => constructors
          | NONE =>
              (case TypeBase.fetch ty of
                   NONE =>
                     raise Fail "quantified type has no TypeBase nchotomy"
                 | SOME info =>
                     let
                       val constructors = map (TypeBasePure.cinst ty)
                         (TypeBasePure.constructors_of info)
                       val _ = constructor_cache :=
                         Redblackmap.insert
                           (!constructor_cache, ty, constructors)
                     in
                       constructors
                     end)

      fun constructor_arguments constructor =
        #1 (boolSyntax.strip_fun (Term.type_of constructor))

      fun validate_exhaustive_shape ancestors expected_depth ty
            (shape as Refute_Eval.CaseShape
              {depth, complete, constructors}) =
        let
          val _ = if complete then ()
            else raise Fail "quantified domain metadata is incomplete"
          val _ = if depth = expected_depth andalso depth >= 0 then ()
            else raise Fail "case-tree depth metadata mismatch"
          val _ = if List.exists (Util.same_type ty) ancestors then
              raise Fail "recursive quantified domain is depth-truncated"
            else ()
          val actual = constructors_of ty
          val _ = if length actual = length constructors then ()
            else raise Fail "case-tree constructor count mismatch"

          fun one (index, (constructor, metadata)) =
            let
              val {id, fields} = metadata
              val argument_types = constructor_arguments constructor
              val _ = if id = index then ()
                else raise Fail "case-tree constructor identity mismatch"
              val _ = if length argument_types = length fields then ()
                else raise Fail "case-tree constructor arity mismatch"
              val child_depth = Int.max (0, depth - 1)
              val _ = if null fields orelse depth > 0 then ()
                else raise Fail "constructor fields truncated at depth zero"
            in
              ListPair.appEq
                (fn (field_ty, field_shape) =>
                  validate_exhaustive_shape (ty :: ancestors) child_depth
                    field_ty field_shape)
                (argument_types, fields)
            end
        in
          List.app one (Lib.enumerate 0
            (ListPair.zip (actual, constructors)))
        end

      fun validate_term ty Refute_Eval.CaseVariable tm =
            if Term.is_var tm andalso
               Util.same_type (Term.type_of tm) ty then ()
            else raise Fail "case variable pattern does not match its term"
        | validate_term ty
            (Refute_Eval.CaseConstructor (id, patterns)) tm =
            let
              val constructors = constructors_of ty
              val constructor = List.nth (constructors, id)
                handle Subscript =>
                  raise Fail "case pattern constructor is out of range"
              val (head, arguments) = boolSyntax.strip_comb tm
              val argument_types = constructor_arguments constructor
              val _ = if Term.aconv head constructor then ()
                else raise Fail "case pattern constructor term mismatch"
              val _ = if length arguments = length patterns andalso
                         length patterns = length argument_types then ()
                else raise Fail "case pattern term arity mismatch"
            in
              ListPair.appEq
                (fn ((argument_ty, pattern), argument) =>
                  validate_term argument_ty pattern argument)
                (ListPair.zip (argument_types, patterns), arguments)
            end

      fun validate_cover shape ty branches =
        let
          (* Poly/ML equality short-circuits on the shared shape DAG's
             pointer-identical nodes, so keep this small local assoc list.
             Constructor lookup above is separately memoized by type. *)
          val size_cache =
            ref ([] :
              (Refute_Eval.case_shape * Arbnum.num) list)

          fun domain_size shape =
            case List.find (fn (cached, _) => cached = shape)
              (!size_cache) of
                SOME (_, size) => size
              | NONE =>
                  let
                    val Refute_Eval.CaseShape {constructors, ...} = shape
                    fun product fields =
                      List.foldl (fn (field, total) =>
                        Arbnum.* (domain_size field, total))
                        Arbnum.one fields
                    val size = List.foldl (fn ({fields, ...}, total) =>
                      Arbnum.+ (product fields, total))
                      Arbnum.zero constructors
                    val _ = size_cache := (shape, size) :: !size_cache
                  in
                    size
                  end

          fun cover_size shape Refute_Eval.CaseVariable =
                domain_size shape
            | cover_size
                (Refute_Eval.CaseShape {constructors, ...})
                (Refute_Eval.CaseConstructor (id, arguments)) =
                let
                  val fields =
                    case List.find (fn {id = other, ...} =>
                      id = other) constructors of
                        SOME {fields, ...} => fields
                      | NONE =>
                          raise Fail "case tree has an extra branch"
                  val _ = if length fields = length arguments then ()
                    else raise Fail "case tree has an extra branch"
                in
                  ListPair.foldlEq (fn (field, argument, total) =>
                    Arbnum.* (cover_size field argument, total))
                    Arbnum.one (fields, arguments)
                end

          fun disjoint
                (Refute_Eval.CaseVariable, _) = false
            | disjoint (_, Refute_Eval.CaseVariable) = false
            | disjoint
                (Refute_Eval.CaseConstructor (left, left_arguments),
                 Refute_Eval.CaseConstructor (right, right_arguments)) =
                left <> right orelse
                ListPair.exists disjoint
                  (left_arguments, right_arguments)

          fun pairwise [] = true
            | pairwise (pattern :: rest) =
                List.all (fn other =>
                  disjoint (pattern, other)) rest andalso
                pairwise rest

          val supplied = map #1 branches
          val sizes = map (cover_size shape) supplied
          (* Patterns are constructor trees over this finite shape.
             Pairwise disjointness makes their cover counts additive, so
             equality with the domain size is exactly the condition that
             every ground value is matched once.  Error priority is fixed
             as extra, overlapping, then missing. *)
          val _ = if pairwise supplied then ()
            else raise Fail "case tree has overlapping branches"
          val covered = List.foldl Arbnum.+ Arbnum.zero sizes
          val _ = if covered = domain_size shape then ()
            else raise Fail "case tree has a missing branch"
          val _ = List.app (fn (pattern, tm, _) =>
            validate_term ty pattern tm) branches
        in
          ()
        end

      fun constructor_key tm =
        let
          val (head, _) = boolSyntax.strip_comb tm
          val {Thy, Name, ...} = Term.dest_thy_const head
        in
          SOME (Thy ^ "$" ^ Name)
        end
        handle Feedback.HOL_ERR _ => NONE

      fun refutation_index patterned_refutations =
        let
          fun add ((pattern, theorem), index) =
            case constructor_key pattern of
                NONE => index
              | SOME key =>
                  Redblackmap.insert
                    (index, key,
                     theorem ::
                       Option.getOpt
                         (Redblackmap.peek (index, key), []))
        in
          List.foldl add
            (Redblackmap.mkDict String.compare)
            patterned_refutations
        end

      fun indexed_refutation index conclusion =
        let
          fun add_key (tm, keys) =
            case constructor_key tm of
                NONE => keys
              | SOME key =>
                  if List.exists (fn old => old = key) keys then keys
                  else key :: keys
          val keys = List.foldl add_key []
            (HolKernel.find_terms (Option.isSome o constructor_key)
              conclusion)
          val candidates = List.mapPartial (fn key =>
            case Redblackmap.peek (index, key) of
                SOME [theorem] => SOME theorem
              | _ => NONE) keys
        in
          case candidates of [theorem] => SOME theorem | _ => NONE
        end

      fun close_from index refutations (goal as (_, conclusion)) =
        let
          fun accept theorem =
            SOME (Tactic.MATCH_ACCEPT_TAC theorem goal)
            handle Feedback.HOL_ERR _ => NONE
          fun scan () = Lib.get_first accept refutations
          (* [validate_cover] has proved the patterns disjoint and
             exhaustive, so at most one refutation can close this leaf.
             A unique constructor-head lookup therefore preserves the
             theorem selected by the old scan.  Ambiguous or finer splits
             deliberately miss the index and retain the linear fallback. *)
          val solved =
            case indexed_refutation index conclusion of
                SOME theorem =>
                  (case accept theorem of
                       SOME result => SOME result
                     | NONE => scan ())
              | NONE => scan ()
        in
        case solved of
            SOME solved => solved
          | NONE =>
              let
                val variables = Term.free_vars_lr conclusion
                fun splittable variable =
                  Option.isSome (TypeBase.fetch (Term.type_of variable))
                val variable =
                  case List.find splittable variables of
                      SOME found => found
                    | NONE => raise Fail
                        "case split did not reach a replay leaf"
                val nchotomy = TypeBase.nchotomy_of
                  (Term.type_of variable)
              in
                Tactical.THEN
                  (Tactic.STRUCT_CASES_TAC
                     (Drule.ISPEC variable nchotomy),
                   close_from index refutations) goal
              end
        end

      fun prove_neg formula Refute_Eval.CaseLeaf =
            let
              val theorem = eval_original formula
              val rhs = rhs_of theorem
            in
              if Term.aconv rhs boolSyntax.F then Drule.EQF_ELIM theorem
              else raise Fail
                ("leaf EVAL did not produce F: " ^ head_name rhs)
            end
        | prove_neg formula
            (Refute_Eval.CaseUniversal {witness, subtree, ...}) =
            let
              val (variable, body) = boolSyntax.dest_forall formula
              val variable_ty = Term.type_of variable
              val _ =
                if Util.same_type variable_ty (Term.type_of witness) then ()
                else raise Fail "universal witness type mismatch"
              val instance = Term.subst
                [{redex = variable, residue = witness}] body
              val refutation = prove_neg instance subtree
              val assumed = Thm.ASSUME formula
              val assumed_instance = Drule.SPECL [witness] assumed
              val falsehood = Thm.MP (Thm.NOT_ELIM refutation)
                assumed_instance
            in
              Thm.NOT_INTRO (Thm.DISCH formula falsehood)
            end
        | prove_neg formula
            (Refute_Eval.CaseExistential {shape, branches}) =
            let
              val _ = if null branches then
                  raise Fail "existential node has no branches"
                else ()
              val (variable, body) = boolSyntax.dest_exists formula
              val _ = validate_exhaustive_shape [] run_depth
                (Term.type_of variable) shape
              val _ = validate_cover shape (Term.type_of variable) branches
              fun branch_refutation (_, pattern, subtree) =
                prove_neg (Term.subst
                  [{redex = variable, residue = pattern}] body) subtree
              val refutations = map branch_refutation branches
              val patterned_refutations =
                ListPair.mapEq (fn ((_, pattern, _), theorem) =>
                  (pattern, theorem)) (branches, refutations)
              val index = refutation_index patterned_refutations
              val all_negated = boolSyntax.mk_forall
                (variable, boolSyntax.mk_neg body)
              val exhaustive = Tactical.prove
                (all_negated,
                 Tactical.THEN
                   (Tactic.GEN_TAC, close_from index refutations))
              val conversion = Conv.CONV_RULE
                (Conv.DEPTH_CONV Thm.BETA_CONV)
                (Drule.ISPEC (Term.mk_abs (variable, body))
                  boolTheory.NOT_EXISTS_THM)
              val target = rhs_of conversion
              val exhaustive = conform_conclusion
                "existential" target exhaustive
            in
              Thm.EQ_MP (Thm.SYM conversion) exhaustive
            end

      val replayed = prove_neg pnf case_tree
      val negated_equality = Thm.AP_TERM boolSyntax.negation prenex_equality
      val replayed = conform_conclusion
        "prenex" (rhs_of negated_equality) replayed
      val certificate = Thm.EQ_MP (Thm.SYM negated_equality) replayed
      val _ = if null (Thm.hyp certificate) then ()
        else raise Fail "replay certificate retained hypotheses"
      val values = map (fn tm => (tm, eval_term env tm)) evals
    in
      Certified (replace cex Refute_Core.Genuine values (SOME certificate))
    end
    handle Interrupt => raise Interrupt
         | error => replay_failure cex (replay_error_text error)
end
