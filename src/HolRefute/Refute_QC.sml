structure Refute_QC = struct
  type term = Term.term
  open Refute_Cert Refute_Eval
  structure SmartGen = Refute_SmartGen
  structure MFH = Refute_ModelFinder_HOL

  val member = Refute_Util.aconv_member

  val union_terms = Refute_Util.union_terms

  fun subtract_terms left right =
    List.filter (fn tm => not (member tm right)) left

  (* A [Bind] fallback needs a generator that can actually run: plan
     construction has no [strategy] in scope (it is strategy-agnostic by
     the same design as [Refute_Gen.spec_of]), so a datatype recursive
     under a function type -- or a container over one, e.g. [:itree
     list] -- must answer [false] here exactly as it did before [spec_of]
     stopped refusing it: exhaustive extraction still rejects the type by
     name (transitively, into every constructor argument), and threading
     a fallback into that plan would only turn the whole extraction's
     refusal into a mid-search one.  [type_recursive_under_function] is
     transitive for exactly this reason; the non-transitive predicate
     answers only for [ty]'s own family and would leave a container's
     [Bind] with a fallback that reaches a rejected element type. *)
  fun genspec_available ty =
    ((case Refute_Gen.spec_of ty of
          Refute_Gen.GenDatatype _ =>
            not (Refute_Gen.type_recursive_under_function ty)
        | _ => true)
     handle Refute_Gen.NoGenerator _ => false)

  fun guarded_gen variable continuation =
    case Refute_Gen.predicate_of (Term.type_of variable) of
      NONE => Gen (variable, continuation)
    | SOME predicate =>
        Gen (variable, Guard {condition = Term.mk_comb (predicate, variable),
          smart = false, cont = continuation})

  fun gen_all variables continuation =
    List.foldr (fn (variable, plan) => guarded_gen variable plan)
      continuation variables

  fun fresh_variables avoids types =
    let
      val avoid_variables = List.concat (List.map Term.free_vars_lr avoids)
      fun fresh avoid ty =
        let val variable = Term.variant avoid (Term.mk_var ("x", ty))
        in (variable, variable :: avoid) end

      fun loop [] avoid variables = rev variables
        | loop (ty :: rest) avoid variables =
            let val (variable, avoid') = fresh avoid ty
            in loop rest avoid' (variable :: variables) end
    in
      loop types avoid_variables []
    end

  (* [use_subtype] rep->abs transport.  For a free variable [x : t] of a
     [MonoInstances] goal where [t] has no generator of its own but is a
     typedef the model finder's registry knows, replace [x] throughout by
     [abs r] for a fresh [r : rty], contract every [rep (abs r)] redex the
     substitution creates back to [r], and guard the goal with the
     (beta-reduced) characteristic predicate applied to [r].  Both the
     variable that was bound by an outer [!] (already free by the time
     [make_instance] hands us [goal], having been stripped) and one that
     was already free look identical here, so one rewrite covers both, as
     the task's "free (Skolemized) variables get the corresponding
     hypothesis form" describes.  [TYPE_DEFINITION P rep] makes [abs]
     restricted to [{r | P r}] a bijection onto [t]; the guard is what
     licenses the contraction (see [Refute_Core.README] and this
     structure's own registration below), not an optimisation on top of
     it -- an unguarded contraction would let a representation value
     outside [t]'s image manufacture a spurious refutation.

     This is a plain rewrite of the goal term consumed by
     [compile_plan_with]/native narrowing alike, so every strategy and
     substrate gets transport from this one place; no plan-IR node and no
     new genspec are involved.  The result is re-normalized exactly as
     [Refute_Core.make_instance] normalizes an ordinary goal (see
     [transport_instance] below): skipping that would leave, say, a
     rewritten [P ==> P] unrecognised as the tautology it is only because
     this rewrite runs after [make_instance]'s own normalization pass.
     Narrowing is the one strategy that does not consume the shared
     plan: it compiles a PNF formula, so it takes [#goal] directly
     rather than through [compile_plan_with], and it takes it *open* --
     [Refute_Narrow.pnf_of] closes free variables itself, which is how
     the fresh representation variables become the prefix's leading
     universals.  See [Refute_QC_Narrow.narrowing_goal], which records
     what measurably goes wrong if they are closed here first. *)

  fun has_generator ty =
    (Refute_Gen.spec_of ty; true) handle Refute_Gen.NoGenerator _ => false

  (* A registered generator, an [abstract_generator] wrapper, or a
     TypeBase datatype all make [spec_of] succeed and must win over
     transport (the firing condition); only then is the model finder's
     lazily-harvested typedef registry consulted.  A goal over [:t list]
     does reach this check -- the free variable's type is [:t list],
     [spec_of] fails for it, so [has_generator] is false and the test
     proceeds -- and what refuses it is [MFH.harvest_typedef]:
     [:t list] is a raw free datatype, one of the classifications its
     own [incompatible] test excludes.  So no container is ever
     transported and the goal keeps today's [NoGenerator]/[Unknown]
     behaviour. *)
  (* [MFH.typedef_for_type] also answers for the synthetic frac/fmap
     entries [MFH.harvest_typedef] admits via its own [is_typedef]
     short-circuit (bypassing that function's [incompatible] test, which
     would otherwise exclude frac): those have no [TYPE_DEFINITION]
     theorem, so [abs] there is not a licensed bijection -- for frac it is
     not even a constant, since [retype_frac_constant] cannot match
     [abs_frac]'s monomorphic generic type to any other carrier and falls
     back to a reserved variable.  [MFH.raw_typedef_data] being [SOME] is
     exactly [register_typedef_unlocked]'s own admission requirement, so
     every genuine entry already satisfies it; requiring it here closes
     the synthetic bypass without disturbing genuine typedefs. *)
  fun transportable_typedef ty =
    if has_generator ty then NONE
    else if MFH.harvest_typedef ty andalso
            Option.isSome (MFH.raw_typedef_data ty)
    then MFH.typedef_for_type ty
    else NONE

  type transport_entry =
    {x : term, r : term, abs : term, rep : term, pred : term}

  fun transport_entries goal evals =
    let
      fun typedef_of variable =
        Option.map (fn info => (variable, info : MFH.typedef_info))
          (transportable_typedef (Term.type_of variable))
      val found = List.mapPartial typedef_of (Term.free_vars_lr goal)
    in
      if null found then []
      else
        let
          val fresh = fresh_variables (goal :: evals)
            (map (#rty o #2) found)
        in
          ListPair.map
            (fn ((x, info : MFH.typedef_info), r) =>
              {x = x, r = r, abs = #abs info, rep = #rep info,
               pred = #pred info} : transport_entry)
            (found, fresh)
        end
    end

  (* [Term.subst] on a non-[Fv] redex walks the term top-down replacing
     every [aconv] occurrence, which is exactly the contraction of
     [rep (abs r)] to [r] this needs; no hand-rolled walker required. *)
  fun apply_transport_entries entries tm =
    let
      val subst = map (fn {x, abs, r, ...} : transport_entry =>
        {redex = x, residue = Term.mk_comb (abs, r)}) entries
    in
      List.foldl
        (fn ({abs, rep, r, ...} : transport_entry, tm) =>
          Term.subst
            [{redex = Term.mk_comb (rep, Term.mk_comb (abs, r)),
              residue = r}] tm)
        (Term.subst subst tm) entries
    end

  fun transport_guard ({pred, r, ...} : transport_entry) =
    MFH.beta_normalize (Term.mk_comb (pred, r))

  (* Installed as [Refute_Core]'s [mono_instance_transform]; runs once per
     [MonoInstances] instance, after monomorphization, before any plan is
     compiled from [#goal]. *)
  fun transport_instance (cfg : Refute_Core.config)
        (instance : Refute_Core.instance) =
    if not (#use_subtype (#qc cfg)) then instance
    else
      case transport_entries (#goal instance) (#evals instance) of
          [] => instance
        | entries =>
            let
              val body = apply_transport_entries entries (#goal instance)
              val raw_goal = List.foldr boolSyntax.mk_imp body
                (map transport_guard entries)
              (* [make_instance] runs every goal through [normalize] (and
                 [expand_quantifiers]) before anything downstream sees it;
                 skipping that step here would let an entirely ordinary
                 simplification -- e.g. the [P ==> P] the docstring's own
                 worked example reduces to once the guard and the
                 contracted body coincide -- go unrecognised only because
                 this rewrite built its implication after that pass ran.
                 Re-running it is what makes a transported goal reach the
                 exact completeness verdict its hand-written equivalent
                 would. *)
              val goal = Refute_Core.expand_quantifiers
                (Refute_Core.strip_outer_forall_body
                   (Refute_Core.normalize raw_goal))
              val evals =
                map (apply_transport_entries entries) (#evals instance)
            in
              { original = #original instance,
                goal = goal,
                qc_gate = Refute_Core.compute_qc_gate goal evals,
                evals = evals,
                card = #card instance,
                size_matters = Refute_Core.instance_size_matters goal,
                transport = map (fn {x, r, abs, ...} : transport_entry =>
                  (r, x, abs)) entries }
            end

  val _ = Refute_Core.register_mono_instance_transform transport_instance

  type analysis =
    {result : SmartGen.inference_result option,
     trigger : bool, reason : string option}

  (* Outcome of one clause acquisition.  [NoClauses (SOME text)] is the
     triggered failure -- a fixpoint group was found but its introduction
     rules did not convert -- and [NoClauses NONE] the untriggered one. *)
  datatype clause_source =
      Clauses of term list * SmartGen.inference_clause list
    | NoClauses of string option

  type plan_cache =
    {smart_context : MFH.mf_context option option ref,
     analyses : (term * analysis) list ref,
     (* Keyed by (relation, position, static value), never by relation
        alone and never by (relation, value) alone: a relation can have
        more than one predicate-typed parameter, and a plan specialised
        to one closed argument at one position must never answer for the
        same value pinned at a different position.  Lookup uses
        [Term.aconv] on the value, exactly like
        [SmartGen.same_relation]/[SmartGen.same_term] do for the
        ordinary cache this one sits beside. *)
     fixed_analyses : (term * int * term * analysis) list ref,
     (* [SmartGen.infer_graph] inference for a function's own graph,
        keyed by the constant alone -- unlike [fixed_analyses], a graph
        inference has no position or static value to specialise. *)
     graph_analyses : (term * analysis) list ref}

  fun new_plan_cache () : plan_cache =
    {smart_context = ref NONE, analyses = ref [], fixed_analyses = ref [],
     graph_analyses = ref []}

  (*
     Plan compilation, ported from exhaustive_generators.ML:260--315.

     compile concl bound [] = gen_all (frees concl \\ bound) (Test concl)
     compile concl bound (a :: rest) =
       if optimise_equality andalso a is (l = r) then
         try_eq (l, r) orelse try_eq (r, l) orelse default
       else default

     try_eq (lhs, x), x a free not in frees(lhs) U bound:
       gen_all (frees a \\ {x})
         (Bind (x, lhs, fallback, compile concl (frees a U bound) rest))
     try_eq (lhs, C a1 ... an), C a fully-applied TypeBase constructor:
       gen_all (frees lhs \\ bound)
         (Split (lhs, [(C, [v1 ... vn],
           compile concl (frees lhs U {vs} U bound)
             ([v1 = a1, ... vn = an] @ rest))]))
     default:
       gen_all (frees a \\ bound)
         (Guard {condition = a, smart = false,
                 cont = compile concl (frees a U bound) rest})
  *)
  fun compile_plan_with
        ({smart_context = smart_context_cache, analyses, fixed_analyses,
          graph_analyses}
           : plan_cache)
        (config : Refute_Core.config) goal =
    let
      val (raw_assumptions, conclusion) = boolSyntax.strip_imp goal
      (* Hoisted, read once for the whole goal -- exactly like
         [smart_context] below -- rather than re-read at every route that
         might want it.  A per-route read has already leaked once in this
         codebase; the single route that consumes it, [positive_candidates]'s
         graph branch, takes this value rather than re-reading the field.
         The graph route is a smart-generator route -- its output is an
         [Enum], exactly like [smart_context]'s callers -- but it cannot
         gate on [smart_context ()] the way they do: they need the
         model-finder context itself, so [NONE] doubles as their veto,
         while [infer_graph] works from [f]'s own defining equations and
         needs no context at all, so it has no such incidental veto and
         must state the [smart_generators] dependency explicitly here.
         Without this conjunct this route would be the only
         smart-generator route not gated by [smart_generators], so
         [strategy_run_body]'s [upd_smart_generators false] (below) would
         fail to keep a random plan [Enum]-free. *)
      val allow_function_inversion =
        #smart_generators (#qc config) andalso
        #allow_function_inversion (#qc config)
      (* [Refute_Core.normalize]'s [AND_IMP_INTRO] folds a multi-premise
         chain into one conjunction before a real goal ever reaches here
         (a bare [compile_plan] call on an unnormalized goal does not);
         flatten it back so each conjunct is classified on its own,
         instead of the whole conjunction being handed to [classify] as
         a single opaque, headless assumption. *)
      val assumptions =
        List.concat (map boolSyntax.strip_conj raw_assumptions)
      (* Building a model-finder context scans the whole theory ancestry,
         so pay for it only once a premise actually reaches mode inference:
         goals without relational premises never need it. *)
      fun smart_context () =
        case !smart_context_cache of
            SOME cached => cached
          | NONE =>
              let
                val built =
                  if #smart_generators (#qc config) then
                    SOME (MFH.make_context (#mf config) [])
                  else NONE
              in
                smart_context_cache := SOME built; built
              end
      fun vars_of bound tm = subtract_terms (Term.free_vars_lr tm) bound

      fun premise_head premise =
        let val (head, _) = HolKernel.strip_comb premise
        in if Term.is_const head then SOME head else NONE end
        handle HOL_ERR _ => NONE

      fun error_text error =
        ((case General.exnMessage error of
              "" => "unexpected mode-inference exception"
            | text => text)
         handle Interrupt => raise Interrupt
              | _ => "unexpected mode-inference exception")

      (* The memoise-and-recover shape shared by the three [analyse*]
         functions below: consult the cache, else compute, cache the
         answer and register any inference it produced.  An exception
         (other than [Interrupt]) is itself cached, as a triggered
         [NONE] carrying its text, so a relation that raises is not
         re-analysed on every candidate.  The caches differ in key
         shape, so each caller supplies its own [find]/[store]. *)
      fun memoised {find, store} compute =
        case find () of
            SOME answer => answer
          | NONE =>
              let
                val answer = compute ()
                val _ = store answer
                val _ = Option.app SmartGen.cache_inference (#result answer)
              in
                answer
              end
              handle Interrupt => raise Interrupt
                   | error =>
                       let
                         val answer =
                           {result = NONE, trigger = true,
                            reason = SOME (error_text error)}
                       in
                         store answer; answer
                       end

      fun safe_term_text tm =
        Parse.term_to_string tm
        handle Interrupt => raise Interrupt
             | _ => "<unprintable premise>"

      (* SCC route first, falling back to the weaker but independent
         single-relation Horn route: a group whose introduction rules the
         SCC converter cannot use is not out of reach.  Exceptions are
         left unhandled here; each caller treats them as it must. *)
      fun clause_source relation =
        let
          fun from_horn fallback =
            case SmartGen.horn_inference_clauses_for relation of
                SOME clauses => Clauses ([relation], clauses)
              | NONE => NoClauses fallback
        in
          case smart_context () of
              NONE => NoClauses NONE
            | SOME context =>
                (case MFH.instantiated_fixpoint_group context relation of
                     NONE => from_horn NONE
                   | SOME {members, rules, ...} =>
                       (case SmartGen.scc_clauses members rules
                               MFH.joint_intro_triple_for of
                            SOME clauses => Clauses (members, clauses)
                          | NONE => from_horn (SOME
                              "introduction-rule conversion failed")))
        end

      fun analyse relation =
        memoised
          {find = fn () =>
             Option.map #2 (List.find (fn (other, _) =>
               SmartGen.same_constant relation other) (!analyses)),
           store = fn answer => analyses := (relation, answer) :: !analyses}
          (fn () =>
             case clause_source relation of
                 Clauses (members, clauses) =>
                   {result = SOME (SmartGen.infer_group
                      {members = members, clauses = clauses, external = [],
                       reorder_premises = #reorder_premises (#qc config)}),
                    trigger = true, reason = NONE}
               | NoClauses reason =>
                   {result = NONE, trigger = Option.isSome reason,
                    reason = reason})

      fun clauses_and_members relation =
        (case clause_source relation of
             Clauses pair => SOME pair
           | NoClauses _ => NONE)
        handle Interrupt => raise Interrupt | _ => NONE

      (* Static-parameter specialisation: [relation]'s argument at
         [position] is pinned to the one closed [value] found at a call
         site, rather than left as the opaque [Fun] mode that a
         higher-order parameter otherwise gets.  Cached by [(relation,
         position, value)] so a plan specialised to one static argument at
         one position is never reused for a different value, nor for the
         same value pinned at a different position (a relation can carry
         more than one predicate-typed parameter), and never mixed with
         the ordinary, value-independent [analyses] cache above. *)
      fun analyse_fixed relation position value =
        memoised
          {find = fn () =>
             Option.map #4 (List.find (fn (other_relation, other_position,
                                            other_value, _) =>
               SmartGen.same_constant relation other_relation andalso
               position = other_position andalso
               SmartGen.same_term value other_value) (!fixed_analyses)),
           store = fn answer => fixed_analyses :=
             (relation, position, value, answer) :: !fixed_analyses}
          (fn () =>
              let
                val answer =
                  case clauses_and_members relation of
                      NONE => {result = NONE, trigger = false, reason = NONE}
                    | SOME (members, clauses) =>
                        (case SmartGen.infer_fixed_argument
                               {members = members, clauses = clauses,
                                external = [], relation = relation,
                                position = position, value = value,
                                reorder_premises =
                                  #reorder_premises (#qc config)} of
                             SOME result =>
                               {result = SOME result, trigger = true,
                                reason = NONE}
                           | NONE =>
                               {result = NONE, trigger = false, reason = NONE})
              in
                answer
              end)

      (* Every position in [call] whose domain is a predicate type and
         whose actual argument there is closed: a candidate for static-
         parameter specialisation.  A non-predicate function parameter
         (no [predicate_mode_of]) is excluded exactly as the ordinary
         mode table already excludes it; an open argument -- one that
         still mentions a bound or as-yet-ungenerated variable -- is
         excluded because it is not yet a single known value to
         specialise to. *)
      fun fixed_argument_positions call =
        let
          val (relation, arguments) = HolKernel.strip_comb call
        in
          if not (Term.is_const relation) then []
          else
            let
              val (domains, _) = boolSyntax.strip_fun (Term.type_of relation)
            in
              List.mapPartial (fn result => result)
                (Lib.mapi (fn index => fn argument =>
                    if index >= length domains then NONE
                    else
                      let val domain = List.nth (domains, index)
                      in
                        if Option.isSome (SmartGen.predicate_mode_of domain)
                           andalso null (Term.free_vars argument)
                        then SOME (relation, index, argument)
                        else NONE
                      end)
                  arguments)
            end
        end
        handle HOL_ERR _ => []

      (* The smart-generator candidate for a premise: a positive
         enumerator for a [Prem]-shaped call, or a complement condition
         for a negated one.  The two never mix -- a mode is a
         [Negative] candidate only via [SmartGen.complement_available],
         which reads the table [Refute_SmartGen.negative_modes_of]
         built, itself derived only from the positive clauses under
         the same mode.  Nothing here compiles a positive program with
         a flipped flag. *)
      datatype smart_source =
          Positive of SmartGen.enumerator
        | Negative of term

      (* Static-parameter specialisation candidates for [assumption]: for
         every closed predicate argument [fixed_argument_positions] finds,
         mode-infer the relation with that one position pinned instead of
         left [Fun]-opaque, and offer whatever positive enumerators that
         inference compiles.  This is additive next to the ordinary,
         value-independent [analyse]/[goal_modes_for_call] path just
         below, using the same [Positive] shape, so [action_for]'s
         existing [compare_score] selection picks the best of the two
         automatically -- a specialised enumerator competes on score, it
         is never forced. *)
      (* Lift the goal modes that have a compiled enumerator into
         positive candidates.  The three routes below -- generic, fixed
         argument, function graph -- differ only in the relation key and
         in where their goal modes come from. *)
      fun positive_for key goal_modes =
        List.mapPartial (fn goal_mode as ({mode, ...} : SmartGen.goal_mode) =>
          Option.map (fn program => (goal_mode, Positive program))
            (SmartGen.enumerator_for key mode)) goal_modes

      fun fixed_positive_candidates bound assumption =
        List.concat (map (fn (relation, position, value) =>
            case #result (analyse_fixed relation position value) of
                NONE => []
              | SOME inference =>
                  positive_for (SmartGen.Predicate relation)
                    (SmartGen.goal_modes_for_call bound assumption inference))
          (fixed_argument_positions assumption))

      (* A graph-premise position is Input (every free variable already
         bound) or Output (a bare unbound variable); a compound term
         still carrying an unbound variable is a pattern, which the mode
         system has no way to express, and refuses the whole premise
         rather than misreading the position as either. *)
      fun graph_position_ok bound term =
        null (vars_of bound term) orelse Term.is_var term

      (* One orientation of an equation as a graph premise: [call] a
         constant applied at exactly its own maximal arity (a partial
         application has no equations to invert, and is refused rather
         than approximated), [result] the other side, every one of the
         flattened [n + 1] positions passing [graph_position_ok].  The
         arity check below is not the load-bearing refusal either:
         [split_arguments]' own "mode arity mismatch" -- reached through
         [top_level_parts] in [SmartGen.graph_modes_for_call] -- rejects
         the same mismatch downstream, so ablating just this check still
         leaves the suite green.  It stays as a cheap early refusal that
         also lets [graph_position_ok] below assume the flattened list
         has exactly arity + 1 positions. *)
      fun graph_orientation bound (call, result) =
        let
          val (head, arguments) = HolKernel.strip_comb call
        in
          if not (Term.is_const head) then NONE
          else
            let
              val arity =
                length (#1 (boolSyntax.strip_fun (Term.type_of head)))
            in
              if length arguments <> arity then NONE
              else
                let val flattened = arguments @ [result]
                in
                  if List.all (graph_position_ok bound) flattened
                  then SOME (head, flattened)
                  else NONE
                end
            end
        end
        handle HOL_ERR _ => NONE

      (* Both orientations of an equation premise -- [f a1 ... an = r]
         and [r = f a1 ... an] -- are independent candidates: either side
         may be the maximally-applied constant to invert, and each is
         checked on its own, exactly as [equality_score]/[try_equality]
         above try both orientations of an ordinary equation. *)
      fun graph_recognise bound assumption =
        case Lib.total boolSyntax.dest_eq assumption of
            NONE => []
          | SOME (left, right) =>
              List.mapPartial (graph_orientation bound)
                [(left, right), (right, left)]

      (* Memoised [SmartGen.infer_graph] for [constant], keyed by the
         constant alone.  Mirrors [analyse]; [cache_inference] on a
         [SOME] result is what makes [compile_premise]'s [GraphPrem]
         branch reachable.  [trigger]/[reason] are dead here -- only
         [#result] is ever read back by [graph_positive_candidates] --
         the [analysis] record shape is reused solely for the same
         cache/[cache_inference] plumbing as [analyse]/[analyse_fixed],
         whose own [NONE] arm this now matches. *)
      fun analyse_graph constant =
        memoised
          {find = fn () =>
             Option.map #2 (List.find (fn (other, _) =>
               SmartGen.same_constant constant other) (!graph_analyses)),
           store = fn answer =>
             graph_analyses := (constant, answer) :: !graph_analyses}
          (fn () =>
              let
                val answer =
                  case SmartGen.infer_graph allow_function_inversion
                         (#reorder_premises (#qc config)) constant of
                      SOME result =>
                        {result = SOME result, trigger = true, reason = NONE}
                    | NONE =>
                        {result = NONE, trigger = false, reason = NONE}
              in
                answer
              end)

      (* Function-inversion candidates for [assumption]: for every
         orientation [graph_recognise] admits, mode-infer that
         constant's own graph and offer whatever positive enumerators
         the inference compiles.  Gated once, here, on the hoisted
         [allow_function_inversion], so with the flag off no [Graph] key
         is ever built.  Additive next to [generic_modes]/[fixed_modes]
         below, using the same [Positive] shape, so a graph enumerator
         only ever competes on score; a negated premise never reaches
         this function, and a graph relation's negative-mode table is
         empty by construction, so it never appears under a negation.
         This [if not allow ...] is not the load-bearing
         check by itself: [analyse_graph] passes the same
         [allow_function_inversion] into [SmartGen.infer_graph], whose
         own [if not allow then NONE] refuses identically, so ablating
         only this line leaves the test suite green.  It stays as a
         cheap early refusal that also skips building a [Graph] key and
         calling [analyse_graph] at all when the route is off. *)
      fun graph_positive_candidates bound assumption =
        if not allow_function_inversion then []
        else
          List.concat (map (fn (constant, arguments) =>
              case #result (analyse_graph constant) of
                  NONE => []
                | SOME inference =>
                    positive_for (SmartGen.Graph constant)
                      (SmartGen.graph_modes_for_call bound constant arguments
                        inference))
            (graph_recognise bound assumption))

      fun positive_candidates bound assumption =
        case premise_head assumption of
            NONE => ([], false, NONE)
          | SOME relation =>
              let val {result, trigger, reason} = analyse relation
                  val inferred =
                    case result of
                        NONE => []
                      | SOME inference => SmartGen.goal_modes_for_call bound
                          assumption inference
                  val generic_modes =
                    positive_for (SmartGen.Predicate relation) inferred
                  val fixed_modes = fixed_positive_candidates bound assumption
                  val graph_modes = graph_positive_candidates bound assumption
                  val modes = generic_modes @ fixed_modes @ graph_modes
                  val trigger = trigger orelse not (null fixed_modes)
                    orelse not (null graph_modes)
                  val reason =
                    if not (null modes) orelse not trigger then reason
                    else if not (null inferred) then SOME
                      "CPS enumerator compilation failed for inferred mode"
                    else SOME (Option.getOpt (reason,
                      "no executable first-order positive mode"))
              in
                (modes, trigger, reason)
              end

      fun negative_candidates bound assumption =
        let val call = boolSyntax.dest_neg assumption
        in
          case premise_head call of
              NONE => ([], false, NONE)
            | SOME relation =>
                let val {result, trigger, reason} = analyse relation
                    val inferred =
                      case result of
                          NONE => []
                        | SOME inference =>
                            List.filter (fn
                                ({mode, ...} : SmartGen.goal_mode) =>
                              SmartGen.complement_available
                                (SmartGen.Predicate relation) mode inference)
                              (SmartGen.goal_modes_for_call bound call
                                inference)
                    val modes =
                      List.mapPartial (fn goal_mode as
                          ({mode, ins, ...} : SmartGen.goal_mode) =>
                        Option.map (fn program =>
                            (goal_mode,
                             Negative (Refute_EvalEnum.negation_condition
                               program ins)))
                          (SmartGen.enumerator_for
                            (SmartGen.Predicate relation) mode)) inferred
                    val reason =
                      if not (null modes) orelse not trigger then reason
                      else if not (null inferred) then SOME
                        "complement compilation failed for inferred mode"
                      else SOME (Option.getOpt (reason,
                        "no executable negative mode"))
                in
                  (modes, trigger, reason)
                end
        end

      fun smart_candidates bound assumption =
        if boolSyntax.is_neg assumption then
          negative_candidates bound assumption
        else positive_candidates bound assumption

      fun report_fallback assumption reason =
        Refute_Core.Private.say 2
          ("Refute smart generator fallback for " ^
           safe_term_text assumption ^ ": " ^ reason ^ "\n")

      datatype premise_action =
          Smart of SmartGen.goal_mode * smart_source
        | Ordinary

      fun orientation_score bound (lhs, rhs) =
        if Term.is_var rhs andalso
           not (member rhs (Term.free_vars_lr lhs)) andalso
           not (member rhs bound)
        then SOME
          {missing = length (vars_of bound lhs), functional = true,
           generator = false, outputs = 1, recursive = false}
        else
          case fully_applied_constructor rhs of
              NONE => NONE
            | SOME (_, arguments) => SOME
                {missing = length (vars_of bound lhs), functional = true,
                 generator = false, outputs = length arguments,
                 recursive = false}

      fun equality_score bound assumption =
        case Lib.total boolSyntax.dest_eq assumption of
            NONE => NONE
          | SOME (left, right) =>
              (case (orientation_score bound (left, right),
                     orientation_score bound (right, left)) of
                   (NONE, other) => other
                 | (other, NONE) => other
                 | (SOME first, SOME second) =>
                     if SmartGen.compare_score (second, first) = LESS
                     then SOME second else SOME first)

      fun ordinary_score bound assumption =
        if #optimise_equality (#qc config) then
          Option.getOpt (equality_score bound assumption,
            {missing = length (vars_of bound assumption),
             functional = false, generator = true, outputs = 0,
             recursive = false})
        else
          {missing = length (vars_of bound assumption),
           functional = false, generator = true, outputs = 0,
           recursive = false}

      fun action_for bound assumption =
        let
          val ordinary = (Ordinary, ordinary_score bound assumption)
          val (modes, trigger, reason) = smart_candidates bound assumption
          fun add ((mode as {score, ...} : SmartGen.goal_mode, program),
                   NONE) = SOME (Smart (mode, program), score)
            | add ((mode as {score, ...} : SmartGen.goal_mode, program),
                   current as SOME (_, old)) =
                if SmartGen.compare_score (score, old) = LESS then
                  SOME (Smart (mode, program), score)
                else current
          val smart = List.foldl add NONE modes
          val best =
            case smart of
                NONE => ordinary
              | SOME (candidate as (_, score)) =>
                  if SmartGen.compare_score (#2 ordinary, score) = LESS
                  then ordinary else candidate
        in
          (best, trigger, reason)
        end

      fun remove_nth selected entries =
        List.map #2 (List.filter (fn (index, _) => index <> selected)
          (Lib.enumerate 0 entries))

      fun select_premise bound entries =
        let
          fun candidate (index, assumption) =
            let val (scored, trigger, reason) = action_for bound assumption
            in (index, assumption, scored, trigger, reason) end
          val first = candidate (0, hd entries)
          val all =
            if #smart_generators (#qc config) andalso
               #reorder_premises (#qc config)
            then map candidate (Lib.enumerate 0 entries)
            else [first]
          val reorder = length all > 1 andalso
            List.exists (fn (_, _, _, trigger, _) => trigger) all
          val candidates = if reorder then all else [first]
          fun least (item as (_, _, (_, score), _, _)) NONE = SOME item
            | least (item as (_, _, (_, score), _, _))
                (current as SOME (_, _, (_, old), _, _)) =
                if SmartGen.compare_score (score, old) = LESS
                then SOME item else current
        in
          (valOf (List.foldl (fn (item, result) => least item result)
             NONE candidates), reorder)
        end

      fun compile conclusion bound assumptions =
        case assumptions of
          [] => gen_all (vars_of bound conclusion) (Test conclusion)
        | _ =>
            let
              val ((selected, assumption, (action, _), triggering, reason),
                   reorder) = select_premise bound assumptions
              val rest = remove_nth selected assumptions
              val assumption_vars = vars_of bound assumption
              val next_bound = union_terms assumption_vars bound
              fun continuation () = compile conclusion next_bound rest

              fun default () =
                gen_all assumption_vars
                  (Guard {condition = assumption, smart = false,
                          cont = continuation ()})

              fun try_equality (lhs, rhs) =
                if Term.is_var rhs andalso
                   not (member rhs (Term.free_vars_lr lhs)) andalso
                   not (member rhs bound)
                then
                  let
                    val fallback =
                      if genspec_available (Term.type_of rhs) then
                        SOME (guarded_gen rhs (continuation ()))
                      else NONE
                    val variables = subtract_terms assumption_vars [rhs]
                  in
                    SOME (gen_all variables
                      (Bind (rhs, lhs, fallback, continuation ())))
                  end
                else
                  case fully_applied_constructor rhs of
                    NONE => NONE
                  | SOME (constructor, arguments) =>
                      let
                        val lhs_variables = vars_of bound lhs
                        val variables = fresh_variables
                          (conclusion :: assumptions @ bound)
                          (List.map Term.type_of arguments)
                        val equations = ListPair.mapEq boolSyntax.mk_eq
                          (variables, arguments)
                        val branch_bound = union_terms lhs_variables
                          (union_terms variables bound)
                        val branch = compile conclusion branch_bound
                          (equations @ rest)
                      in
                        SOME (gen_all lhs_variables
                          (Split (lhs, [(constructor, variables, branch)])))
                      end

              fun ordinary () =
                if #optimise_equality (#qc config) then
                  case Lib.total boolSyntax.dest_eq assumption of
                    NONE => default ()
                  | SOME (left, right) =>
                      let
                        val orientations =
                          if not reorder then
                            [(left, right), (right, left)]
                          else
                            (case (orientation_score bound (left, right),
                                   orientation_score bound (right, left)) of
                                 (SOME first, SOME second) =>
                                   if SmartGen.compare_score
                                        (second, first) = LESS
                                   then [(right, left), (left, right)]
                                   else [(left, right), (right, left)]
                               | _ => [(left, right), (right, left)])
                      in
                        case Lib.get_first try_equality orientations of
                            SOME result => result
                          | NONE => default ()
                      end
                else default ()
            in
              case action of
                  Smart ({mode, ins, outs, missing, ...},
                         Positive {relation, version, ...}) =>
                    gen_all missing
                      (if null outs then
                         (case relation of
                              (* [graph_modes_for_call] already refuses an
                                 all-input mode, so this is unreached today
                                 -- defence in depth against the trap
                                 [Refute_SmartGen.graph_modes_for_call]'s
                                 own comment names: a [Graph] [SmartGuard]'s
                                 [predicate] is an equation, so
                                 [smart_guard_lookup]'s [strip_comb] finds
                                 no matching [Predicate] program, and
                                 [validate_plan] rejects the whole plan as
                                 stale.  Falling back to the ordinary
                                 [Guard] is sound and total: the equation
                                 is exactly as checkable as the plain route
                                 would have made it. *)
                              SmartGen.Graph _ =>
                                Guard {condition = assumption,
                                       smart = false,
                                       cont = continuation ()}
                            | SmartGen.Predicate _ =>
                                (Refute_Core.Private.say 2
                                   ("Refute smart generator Guard for " ^
                                    safe_term_text assumption ^ "\n");
                                 SmartGuard
                                   {predicate = assumption, version = version,
                                    cont = continuation ()}))
                       else
                         Enum {rel = relation, mode = mode, version = version,
                               ins = ins, outs = outs,
                               cont = continuation ()})
                | Smart ({missing, ...}, Negative condition) =>
                    gen_all missing
                      (Refute_Core.Private.say 2
                         ("Refute smart complement Guard for " ^
                          safe_term_text assumption ^ "\n");
                       Guard {condition = condition, smart = true,
                              cont = continuation ()})
                | Ordinary =>
                    (if triggering then
                       report_fallback assumption
                         (Option.getOpt (reason,
                           "no executable first-order positive mode"))
                     else ();
                     ordinary ())
            end
    in
      if #smart_quantifier (#qc config) then
        compile conclusion [] assumptions
      else
        gen_all (Term.free_vars_lr goal) (Test goal)
    end

  fun compile_plan config goal =
    compile_plan_with (new_plan_cache ()) config goal

  fun pp_plan plan =
    let
      fun indent depth = String.implode (List.tabulate (depth, fn _ => #" "))
      fun show depth current =
        case current of
          Test tm => indent depth ^ "Test " ^ Parse.term_to_string tm
        | Gen (variable, continuation) =>
            indent depth ^ "Gen " ^ Parse.term_to_string variable ^ "\n" ^
            show (depth + 2) continuation
        | Bind (variable, expression, fallback, continuation) =>
            indent depth ^ "Bind " ^ Parse.term_to_string variable ^ " = " ^
            Parse.term_to_string expression ^
            (case fallback of NONE => "\n" | SOME plan =>
               "\n" ^ indent (depth + 2) ^ "fallback\n" ^
               show (depth + 4) plan ^ "\n") ^
            show (depth + 2) continuation
        | Split (scrutinee, branches) =>
            let
              fun branch (constructor, variables, continuation) =
                indent (depth + 2) ^ Parse.term_to_string constructor ^ " " ^
                String.concatWith " "
                  (List.map Parse.term_to_string variables) ^
                "\n" ^ show (depth + 4) continuation
            in
              indent depth ^ "Split " ^ Parse.term_to_string scrutinee ^ "\n" ^
              String.concatWith "\n" (List.map branch branches)
            end
        | Guard {condition, smart, cont} =>
            indent depth ^ (if smart then "Complement Guard " else "Guard ") ^
            Parse.term_to_string condition ^ "\n" ^ show (depth + 2) cont
        | SmartGuard {predicate, cont, ...} =>
            indent depth ^ "Smart Guard " ^
            Parse.term_to_string predicate ^ "\n" ^
            show (depth + 2) cont
        | Enum {rel, mode, ins, outs, cont, ...} =>
            indent depth ^ "Enum " ^ SmartGen.relation_string rel ^ "[" ^
            SmartGen.mode_string mode ^ "] (" ^
            String.concatWith ", " (map Parse.term_to_string ins) ^
            ") -> (" ^
            String.concatWith ", " (map Parse.term_to_string outs) ^
            ")\n" ^ show (depth + 2) cont
        | Prune => indent depth ^ "Prune"
    in
      show 0 plan
    end

  fun schedule instances size =
    let
      val cards = List.map #card instances
      val size_matters = List.exists #size_matters instances
      fun compare ((card1, size1), (card2, size2)) =
        case Int.compare (card1 + size1, card2 + size2) of
            EQUAL => Int.compare (card1, card2)
          | order => order
    in
      if size_matters then
        Listsort.sort compare (List.concat (List.map (fn card =>
          List.tabulate (Int.max (0, size), fn index => (card, index + 1)))
          cards))
      else
        List.map (fn card => (card, size)) cards
    end

  datatype schedule_cursor =
      FixedSchedule of (int * int) list
    | AdaptiveSchedule of
        (int * int) list * (int * int) list

  fun entry_before ((card1, size1), (card2, size2)) =
    card1 + size1 < card2 + size2 orelse
    (card1 + size1 = card2 + size2 andalso card1 < card2)

  fun entry_compare (left, right) =
    if entry_before (left, right) then LESS
    else if entry_before (right, left) then GREATER
    else EQUAL

  fun insert_entry entry [] = [entry]
    | insert_entry entry (first :: rest) =
        if entry_before (entry, first) then entry :: first :: rest
        else first :: insert_entry entry rest

  fun schedule_cursor instances size mode =
    let
      val initial = schedule instances size
      val size_matters = List.exists #size_matters instances
    in
      case mode of
          Refute_Core.FixedBound => FixedSchedule initial
        | Refute_Core.IterativeDeepening =>
            if not size_matters then FixedSchedule initial
            else
              AdaptiveSchedule (initial,
                Listsort.sort entry_compare
                  (map (fn instance =>
                    (#card instance, Int.max (0, size) + 1)) instances))
    end

  fun schedule_next (FixedSchedule []) = NONE
    | schedule_next (FixedSchedule (entry :: rest)) =
        SOME (entry, FixedSchedule rest)
    | schedule_next (AdaptiveSchedule (entry :: rest, frontier)) =
        SOME (entry, AdaptiveSchedule (rest, frontier))
    | schedule_next (AdaptiveSchedule ([], [])) = NONE
    | schedule_next
        (AdaptiveSchedule ([], (entry as (card, size)) :: frontier)) =
        SOME (entry, AdaptiveSchedule ([],
          insert_entry (card, size + 1) frontier))

  fun elapsed_msec start =
    LargeInt.toInt (Time.toMilliseconds (Time.- (Time.now (), start)))
    handle Interrupt => raise Interrupt | _ => 0

  fun pnf_replay_eligible case_tree genuine =
    Option.isSome case_tree andalso genuine

  fun case_tree_incomplete Refute_Eval.CaseLeaf = false
    | case_tree_incomplete
        (Refute_Eval.CaseUniversal
          {shape = Refute_Eval.CaseShape {complete, ...}, subtree, ...}) =
        not complete orelse case_tree_incomplete subtree
    | case_tree_incomplete
        (Refute_Eval.CaseExistential
          {shape = Refute_Eval.CaseShape {complete, ...}, branches}) =
        not complete orelse List.exists
          (case_tree_incomplete o #3) branches

  (* Report against the same prenex form the narrowing compiler consumed. *)
  fun pnf_case_bindings prefix tree =
    Refute_Narrow.case_bindings prefix tree

  fun strategy_name Exhaustive = "exhaustive"
    | strategy_name (Random _) = "random"
    | strategy_name Narrowing = "narrowing"

  fun record_candidate_with display_name
        {config : Refute_Core.config,
         strategy : strategy,
         substrate : string,
         instance : Refute_Core.instance,
         stats : (string * int) list,
         counterexamples : Refute_Core.counterexample list ref,
         discarded : int ref,
         run_depth : int option,
         pnf_prefix : (quant * term) list option,
         retain_replay_potential : Refute_Core.counterexample -> unit,
         retry : bool -> candidate list -> unit,
         retry_potential : bool -> candidate list -> unit}
        {env, ground_env, case_tree, genuine, genuine_only, ignored} =
    let
      val bindings = List.filter
        (fn (variable, _) =>
          List.exists (fn free => Term.aconv free variable)
            (Term.free_vars_lr (#goal instance)))
        env
      val report_bindings =
        case (pnf_prefix, case_tree, genuine) of
            (SOME prefix, SOME tree, true) =>
              pnf_case_bindings prefix tree
          | _ => bindings
      val narrowing =
        case strategy of Narrowing => true | _ => false
      (* The plan substrates build their environment by consing, so goal
         order is recovered by reversing.  Narrowing reports against the
         prenex prefix, which is already in goal order. *)
      val goal_ordered_bindings =
        if narrowing then report_bindings else rev report_bindings
      (* [use_subtype] transport reports the user's own variable, not the
         representation-typed [r] testing actually bound: a binding for
         [r] becomes one for [x = abs r-value], per [#transport instance].
         Display only, on the same choke point as [canonicalize_term]
         below -- testing and certification only ever see the untouched
         [env] this function closes over. *)
      fun apply_report_transport (variable, value) =
        case List.find (fn (r, _, _) => Term.aconv r variable)
               (#transport instance) of
            SOME (_, x, abs) => (x, Term.mk_comb (abs, value))
          | NONE => (variable, value)
      (* Display only, via the model finder's own bottom-up walk
         (Refute_ModelFinder_Model.postprocess_term): a registered
         family's canonical form (e.g. fmap's FUPDATE-chain collapse,
         reached through the callback [Refute.sml] installs) never
         reaches testing or certification, both of which still see the
         raw [env] this function closes over.  One registry, one walk,
         one safety contract -- shared with the model finder's own
         display, not a second copy of it. *)
      val postprocessors =
        Refute_ModelFinder_Model.snapshot_term_postprocessors ()
      fun canonicalize_term candidate =
        Refute_ModelFinder_Model.postprocess_term postprocessors candidate
      fun canonicalize (variable, value) = (variable, canonicalize_term value)
      val ordered_bindings = List.map
        (canonicalize o apply_report_transport) goal_ordered_bindings
      val cex : Refute_Core.counterexample =
        { backend = display_name strategy,
          substrate = substrate,
          certainty = if genuine then Refute_Core.Potential []
            else Refute_Core.Potential ["evaluation stuck during testing"],
          bindings = ordered_bindings,
          evals = [], cert = NONE, scope = NONE, model = NONE,
          stats = stats }
      val next =
        {env = env, ground_env = ground_env, case_tree = case_tree,
         genuine = genuine, run_depth = run_depth} :: ignored
      val incomplete_pnf =
        case case_tree of
            SOME tree => not genuine andalso case_tree_incomplete tree
          | NONE => false
      val has_hole = List.exists
        (Refute_ModelFinder_Names.contains_irrelevant_marker o #2) env
      val partial_universal =
        narrowing andalso has_hole andalso
        not (Refute_Narrow.contains_existentials
          (Option.getOpt (pnf_prefix, [])))
      fun keep_potential potential =
        if #abort_potential config andalso not genuine_only then
          (counterexamples := potential :: !counterexamples; true)
        else if genuine_only then
          (retry_potential true next; false)
        else
          (Refute_Core.report_outcome config
             (Refute_Core.Counterexample [potential]);
           retry_potential true next;
           false)
    in
      (* Certification opt-out applies only to an algorithmically genuine
         hit.  A PNF hit tainted by finite-domain approximation remains
         Potential when replay is disabled.  With certification enabled,
         ordinary certification may still prove the original proposition
         false and safely upgrade it; only semantically complete case trees
         are themselves replayed as exhaustive proofs. *)
      if incomplete_pnf andalso not (#certify (#qc config)) then
        (keep_potential (Refute_Cert.replace cex
           (Refute_Core.Potential
             ["PNF testing used an incomplete finite approximation"])
           [] NONE);
         ())
      else if not genuine andalso
          (not (narrowing andalso Option.isSome case_tree)
           orelse not (#certify (#qc config))) then
        (keep_potential (Refute_Cert.replace cex
           (Refute_Core.Potential ["evaluation stuck during testing"])
           [] NONE);
         ())
      else if not (#certify (#qc config)) then
        counterexamples :=
          Refute_Cert.replace cex Refute_Core.Genuine [] NONE ::
          !counterexamples
      else
        let
          val certification =
            case case_tree of
                SOME tree =>
                  if genuine then
                    Refute_Cert_Narrow.certify_case_tree
                      {original = #original instance,
                       evals = #evals instance, env = env,
                       run_depth = Option.getOpt (run_depth, ~1),
                       case_tree = tree, cex = cex}
                  else
                    Refute_Cert.certify
                      {original = #original instance,
                       evals = #evals instance, env = env, cex = cex}
              | NONE =>
                  if partial_universal then
                    Refute_Cert.ground_and_certify
                      {original = #original instance,
                       evals = #evals instance, env = env,
                       ground_env = ground_env, cex = cex}
                  else
                    Refute_Cert.certify
                      {original = #original instance,
                       evals = #evals instance, env = env, cex = cex}
        in
          case certification of
               Refute_Cert.Certified certified =>
                 counterexamples := certified :: !counterexamples
             | Refute_Cert.Uncertified uncertified =>
                 if incomplete_pnf orelse not genuine then
                   ignore (keep_potential (Refute_Cert.replace uncertified
                     (Refute_Core.Potential
                       [if incomplete_pnf then
                          "PNF testing used an incomplete finite " ^
                          "approximation"
                        else "evaluation stuck during testing"])
                     [] NONE))
                 else
                   counterexamples := uncertified :: !counterexamples
             | Refute_Cert.Discarded =>
                 (discarded := !discarded + 1;
                  retry genuine_only next)
             | Refute_Cert.Potential potential =>
                 let
                   val reported =
                     if incomplete_pnf then
                       Refute_Cert.replace potential
                         (Refute_Core.Potential
                           ["PNF testing used an incomplete finite " ^
                            "approximation"])
                         [] NONE
                     else potential
                 in
                   if keep_potential reported andalso
                      Option.isSome case_tree
                   then retain_replay_potential reported
                   else ()
                 end
        end
    end

  fun record_candidate arguments candidate =
    record_candidate_with strategy_name arguments candidate

  fun plan_has_gen current =
    case current of
        Test _ => false
      | Gen _ => true
      | Bind (_, _, fallback, next) =>
          plan_has_gen next orelse
          (case fallback of
               NONE => false
             | SOME alternative => plan_has_gen alternative)
      | Split (_, branches) =>
          List.exists (fn (_, _, next) => plan_has_gen next) branches
      | Guard {cont, ...} => plan_has_gen cont
      | SmartGuard {cont, ...} => plan_has_gen cont
      | Enum _ => true
      | Prune => false

  fun eval_preflight evals =
    let
      val constants = Refute_Core.nonexecutable_constants evals
      val has_binder = List.exists (fn tm =>
        not (null (HolKernel.find_terms Term.is_abs tm))) evals
    in
      (if has_binder then
         ["smart preflight eval contains an unexpanded binder"]
       else []) @
      (if null constants then []
       else ["smart preflight eval is nonexecutable: " ^
         Refute_Core.show_constants constants])
    end

  fun substrate_name Refute_Core.Compute = SOME "compute"
    | substrate_name Refute_Core.Cv = SOME "cv"
    | substrate_name Refute_Core.NativeSML = SOME "native"
    | substrate_name Refute_Core.Auto = NONE

  (* Candidate counters aggregated across every substrate call in one
     search -- one per schedule entry for exhaustive, one per random
     chunk or narrowing window, plus certification retries -- so both the
     witness and the vacuity reason reflect the whole run, never a single
     call's sample.  [absorb] takes one call's stats; a substrate that
     does not report all three keys (as opposed to reporting zero) turns
     the totals off for the rest of the run.  [decorate] replaces the
     substrate's own per-call copies of the three keys with the run
     totals.  Shared with [Refute_QC_Narrow], whose run body needs the
     same three counters over the same three-way discipline. *)
  fun new_counter_totals () =
    let
      val assumption_satisfied = ref 0
      val conclusion_evaluated = ref 0
      val candidates_generated = ref 0
      val measured = ref true
      fun is_counter key =
        key = "assumption_satisfied" orelse key = "conclusion_evaluated"
        orelse key = "candidates_generated"
      fun absorb call_stats =
        case (Refute_Core.lookup_stat "assumption_satisfied" call_stats,
              Refute_Core.lookup_stat "conclusion_evaluated" call_stats,
              Refute_Core.lookup_stat "candidates_generated" call_stats) of
            (SOME satisfied, SOME evaluated, SOME generated) =>
              (assumption_satisfied := !assumption_satisfied + satisfied;
               conclusion_evaluated := !conclusion_evaluated + evaluated;
               candidates_generated := !candidates_generated + generated)
          | _ => measured := false
      fun decorate stats =
        List.filter (fn (key, _) => not (is_counter key)) stats @
        (if !measured then
           [("assumption_satisfied", !assumption_satisfied),
            ("conclusion_evaluated", !conclusion_evaluated),
            ("candidates_generated", !candidates_generated)]
         else [])
      fun reason () =
        if !measured then
          "candidates generated " ^ Int.toString (!candidates_generated) ^
          ", assumptions satisfied " ^
          Int.toString (!assumption_satisfied) ^
          ", conclusions evaluated " ^
          Int.toString (!conclusion_evaluated)
        else "candidate counters unavailable on this substrate"
    in
      {absorb = absorb, decorate = decorate, reason = reason}
    end

  fun add_reason reason reasons =
    if List.exists (fn old => old = reason) (!reasons) then ()
    else reasons := !reasons @ [reason]

  datatype selected_compile =
      Selected of string * compiled_test
    | SelectionFailed of string list

  (* A smart-gate compilation owns backend resources.  Calls can re-enter
     Refute, so cache it by the dynamically propagated call token rather
     than in one process-global slot. *)
  val smart_gate_cache =
    ref ([] : (unit ref * plan list * selected_compile) list)
  val smart_gate_mutex = Mutex.mutex ()

  fun smart_gate_context () =
    case Thread_Data.get Refute_Core.active_refute_context of
        SOME context => context
      | NONE => raise Fail "Refute_QC: no active Refute call"

  fun same_terms left right =
    length left = length right andalso
    ListPair.allEq (fn (left, right) => Term.aconv left right)
      (left, right)

  fun same_plan (Test left, Test right) = Term.aconv left right
    | same_plan (Gen (left_var, left_next),
                 Gen (right_var, right_next)) =
        Term.aconv left_var right_var andalso
        same_plan (left_next, right_next)
    | same_plan
        (Bind (left_var, left_rhs, left_fallback, left_next),
         Bind (right_var, right_rhs, right_fallback, right_next)) =
        Term.aconv left_var right_var andalso
        Term.aconv left_rhs right_rhs andalso
        (case (left_fallback, right_fallback) of
             (NONE, NONE) => true
           | (SOME left, SOME right) => same_plan (left, right)
           | _ => false) andalso
        same_plan (left_next, right_next)
    | same_plan (Split (left_tm, left_branches),
                 Split (right_tm, right_branches)) =
        let
          fun same_branch
                ((left_constructor, left_vars, left_next),
                 (right_constructor, right_vars, right_next)) =
            Term.aconv left_constructor right_constructor andalso
            same_terms left_vars right_vars andalso
            same_plan (left_next, right_next)
        in
          Term.aconv left_tm right_tm andalso
          length left_branches = length right_branches andalso
          ListPair.allEq same_branch (left_branches, right_branches)
        end
    | same_plan (Guard {condition = left_tm, smart = left_smart,
                        cont = left_next},
                 Guard {condition = right_tm, smart = right_smart,
                        cont = right_next}) =
        Term.aconv left_tm right_tm andalso left_smart = right_smart andalso
        same_plan (left_next, right_next)
    | same_plan
        (SmartGuard {predicate = left_predicate, version = left_version,
                     cont = left_next},
         SmartGuard {predicate = right_predicate, version = right_version,
                     cont = right_next}) =
        Term.aconv left_predicate right_predicate andalso
        SmartGen.same_program_version (left_version, right_version) andalso
        same_plan (left_next, right_next)
    | same_plan
        (Enum {rel = left_rel, mode = left_mode, version = left_version,
               ins = left_ins, outs = left_outs, cont = left_next},
         Enum {rel = right_rel, mode = right_mode, version = right_version,
               ins = right_ins, outs = right_outs, cont = right_next}) =
        SmartGen.same_relation left_rel right_rel andalso
        SmartGen.eq_mode (left_mode, right_mode) andalso
        SmartGen.same_program_version (left_version, right_version) andalso
        same_terms left_ins right_ins andalso
        same_terms left_outs right_outs andalso
        same_plan (left_next, right_next)
    | same_plan (Prune, Prune) = true
    | same_plan _ = false

  fun same_plans left right =
    length left = length right andalso
    ListPair.allEq same_plan (left, right)

  (* Substrates are public extension points, so a cleanup callback gets a
     thread and a deadline of its own.  Two properties have to hold at once.

     A cleanup that runs to completion wins, however long it takes.  Cleanup
     is work that may not be torn in half — Cv reverts its theory snapshot
     inside [Thread_Attributes.uninterruptible], because a half-reverted
     snapshot would strand Refute definitions in the user's theory, which is
     exactly the invariant cleanup exists to keep — and theory hygiene is the
     stronger of the two invariants here.  Preemption was never on offer
     anyway: [Timeout.apply] cancels by interrupting the calling thread, and
     Poly/ML defers a masked thread's directed interrupt until the mask
     ends, i.e. until after the cleanup has done all of its work, so its
     expiry could only mislabel a cleanup that had in fact succeeded.  That
     spurious [Timeout.TIMEOUT] escaped [strategy_run] into [run_backend],
     which charged it to the backend's own deadline and discarded a verdict
     the search had already reached.

     A cleanup that never returns must not take the run down with it.  So the
     cleanup runs on its own masked thread and the caller stops *waiting* on
     it after [cleanup_timeout] rather than trying to interrupt it: control
     always comes back, and a cleanup still in progress is reported as
     [CleanupAbandoned] rather than as a search result.  The wait itself is
     masked, so that a run whose own deadline has already expired reports its
     own result instead of having the pending interrupt abort the cleanup.

     Masked, but not deaf.  HOL's Ctrl-C is [Thread.broadcastInterrupt], and
     a broadcast aimed at a thread that is not accepting one is dropped
     outright rather than retained the way a directed interrupt is, so a
     plain mask over a ten-second wait would silently eat the user's first
     Ctrl-C.  The wait therefore steps through
     [ParList.uninterruptible_wait]: the cleanup is still waited out in
     full, and the interrupt is reported afterwards, as a result rather than
     as a raise, so that a caller closing several tests still closes them
     all before the interrupt surfaces.

     An abandoned cleanup leaks its thread.  That is deliberate: Poly/ML
     cannot cancel masked work, and cancelling it is precisely what must not
     happen.  Such a thread keeps whatever the cleanup holds, including
     [Refute_EvalEnum]'s theory lock, but that lock is taken by interruptible
     polling and released without regard to which thread took it, so later
     calls wait interruptibly instead of deadlocking.

     The bound is generous because it now really does abandon work rather
     than merely relabel it: a correct cv cleanup routinely costs 50-260ms,
     so anything near that is a knife edge, whereas the only cost of a large
     bound is how long a substrate that has already broken its contract can
     stall one close.  A ref so that tests can shorten it. *)
  val cleanup_timeout = ref (Time.fromSeconds 10)

  exception CleanupAbandoned of string

  fun bounded_close close =
    let
      val bound = !cleanup_timeout
      val outcome = Synchronized.var "Refute substrate cleanup"
        (NONE : unit Exn.result option)
      fun body () =
        let val result = Exn.capture close ()
        in Synchronized.change outcome (fn _ => SOME result) end
      val _ = Standard_Thread.fork
        {name = "refute-cleanup", stack_limit = NONE, interrupts = false} body
      val deadline = Time.now () + bound
      fun attempt () =
        Synchronized.timed_access outcome (fn _ => SOME deadline)
          (Option.map (fn result => (result, SOME result)))
      (* One last look after the wait expires: a cleanup that completed as
         the deadline passed has still completed, and reporting it would be
         the old defect again, merely at a boundary rather than routinely. *)
      val finished = Exn.capture
        (ParList.uninterruptible_wait (fn observe => fn () =>
          let
            (* An interrupt seen here is recorded, never allowed to cut the
               wait short; the deadline is absolute, so resuming masked
               leaves the bound exactly as it was. *)
            fun wait () =
              case observe attempt () of
                  SOME answer => answer
                | NONE => wait ()
          in
            case wait () of
                SOME result => SOME result
              | NONE => Synchronized.value outcome
          end)) ()
    in
      case finished of
          Exn.Exn error => Exn.Exn error
        | Exn.Res (SOME result) => result
        | Exn.Res NONE =>
            Exn.Exn (CleanupAbandoned
              ("substrate cleanup did not return within " ^
               Time.toString bound ^ "s and was abandoned"))
    end

  fun close_selection (SelectionFailed _) = ()
    | close_selection (Selected (_, test)) =
        Exn.release (bounded_close (#close test))

  fun same_smart_gate_context (left, right) =
    Portable.pointer_eq (left, right)

  fun remove_smart_gate_selection context =
    Multithreading.synchronized "Refute smart gate cache" smart_gate_mutex
      (fn () =>
        let
          fun remove [] kept = (NONE, List.rev kept)
            | remove ((entry as (old_context, plans, selection)) :: rest) kept =
                if same_smart_gate_context (context, old_context) then
                  (SOME (plans, selection), List.revAppend (kept, rest))
                else remove rest (entry :: kept)
          val (selection, cache) = remove (!smart_gate_cache) []
          val _ = smart_gate_cache := cache
        in
          selection
        end)

  fun clear_smart_gate_cache () =
    case remove_smart_gate_selection (smart_gate_context ()) of
        NONE => ()
      | SOME (_, selection) => close_selection selection

  fun store_smart_gate_selection plans selection =
    let
      val context = smart_gate_context ()
      val old = remove_smart_gate_selection context
      val _ = Option.app (close_selection o #2) old
    in
      Multithreading.synchronized "Refute smart gate cache" smart_gate_mutex
        (fn () => smart_gate_cache :=
          (context, plans, selection) :: !smart_gate_cache)
    end

  fun take_smart_gate_selection plans =
    case remove_smart_gate_selection (smart_gate_context ()) of
        NONE => NONE
      | SOME (cached_plans, selection) =>
          if same_plans cached_plans plans then SOME selection
          else (close_selection selection; NONE)

  datatype substrate_candidates =
      Candidates of {explicit : bool, substrates : substrate list}
    | CandidatesUnavailable of string list

  fun ordered_substrate_candidates (config : Refute_Core.config) =
    case #substrate (#qc config) of
        Refute_Core.Auto =>
          Candidates {explicit = false, substrates = get_substrates ()}
      | choice =>
          let val name = valOf (substrate_name choice)
          in
            case List.find (fn substrate => #name substrate = name)
              (get_substrates ()) of
                NONE => CandidatesUnavailable
                  ["requested substrate " ^ name ^ " is unavailable"]
              | SOME substrate =>
                  Candidates {explicit = true, substrates = [substrate]}
          end

  fun say_selected name explicit =
    Refute_Core.Private.say 2
      ("Refute substrate selection: selected " ^ name ^
       (if explicit then " (explicit)" else "") ^ "\n")

  fun say_inapplicable name reasons =
    Refute_Core.Private.say 2
      ("Refute substrate selection: " ^ name ^
       " is inapplicable: " ^
       (if null reasons then "no reason supplied"
        else String.concatWith "; " reasons) ^ "\n")

  (* Gate preflight and execution must walk this same registry snapshot and
     apply the same Auto fallthrough.  In particular, a higher-priority
     custom substrate cannot be skipped while a built-in opens the gate. *)
  fun select_registered config report problem attempt =
    case ordered_substrate_candidates config of
        CandidatesUnavailable reasons => SelectionFailed reasons
      | Candidates {explicit, substrates} =>
          let
            fun failed [] =
                  if explicit then [] else ["no substrate is registered"]
              | failed reasons = reasons
            fun try [] reasons = SelectionFailed (failed reasons)
              | try (substrate :: rest) reasons =
                  (case if #accepts substrate problem then
                          attempt substrate
                        else
                          Inapplicable
                            ["substrate does not accept this problem"] of
                       Compiled test =>
                         (if report then
                            say_selected (#name substrate) explicit
                          else ();
                          Selected (#name substrate, test))
                     | Inapplicable why =>
                         (if report then
                            say_inapplicable (#name substrate) why
                          else ();
                          if explicit then SelectionFailed why
                          else try rest (reasons @ map (fn reason =>
                            #name substrate ^ ": " ^ reason) why)))
          in
            try substrates []
          end

  fun preflight_substrate (substrate : substrate) config strategy plans evals =
    case eval_preflight evals of
        reasons as _ :: _ => Inapplicable reasons
      | [] =>
          let
            val substrate_reasons =
              case #preflight substrate of
                  NONE => []
                | SOME preflight => preflight config strategy plans evals
          in
            if null substrate_reasons then
              #compile substrate config strategy (Plans plans)
            else Inapplicable substrate_reasons
          end

  (* [select_registered] already reads the configured substrate choice and
     applies the Auto fallthrough, so there is nothing left to dispatch on
     here. *)
  fun compile_selected config strategy problem =
    select_registered config true problem (fn substrate =>
      #compile substrate config strategy problem)

  fun compile_smart_selected config report strategy plans evals =
    select_registered config report (Plans plans) (fn substrate =>
      preflight_substrate substrate config strategy plans evals)

  fun smart_gate_override_with select (config : Refute_Core.config)
        instances =
    let
      val _ = clear_smart_gate_cache ()
      val cache = new_plan_cache ()
      val plans = map (fn (instance : Refute_Core.instance) =>
        compile_plan_with cache config (#goal instance)) instances
      val gated_plans = List.mapPartial
        (fn (instance, plan) =>
          case #qc_gate instance of NONE => NONE | SOME _ => SOME plan)
        (ListPair.zip (instances, plans))
      val evals = List.concat
        (map (fn (instance : Refute_Core.instance) => #evals instance)
          instances)
      val eligible =
        #smart_generators (#qc config) andalso
        not (null gated_plans) andalso
        List.all Refute_Eval.plan_uses_smart gated_plans
    in
      if not eligible then false
      else
        case select config Exhaustive plans evals of
            SelectionFailed _ => false
          | selection as Selected _ =>
              (store_smart_gate_selection plans selection; true)
    end
    handle Interrupt =>
             (ignore (Exn.capture clear_smart_gate_cache ()); raise Interrupt)
         | _ =>
             (ignore (Exn.capture clear_smart_gate_cache ()); false)

  fun smart_gate_override config instances =
    smart_gate_override_with
      (fn config => fn strategy => fn plans => fn evals =>
        compile_smart_selected config true strategy plans evals)
      config instances

  fun bounded_size size = Int.max (0, size)

  fun strategy_seed (config : Refute_Core.config) =
    case #seed (#qc config) of
        SOME seed => normalize_seed (IntInf.fromInt seed)
      | NONE => take_session_seed ()

  fun is_random (Random _) = true
    | is_random Exhaustive = false
    | is_random Narrowing = false

  fun close_tests tests =
    let
      fun close ((test : compiled_test), NONE) =
            (case bounded_close (#close test) of
                 Exn.Res _ => NONE
               | Exn.Exn error => SOME error)
        | close ((test : compiled_test), found) =
            (ignore (bounded_close (#close test)); found)
    in
      case List.foldl close NONE tests of
          NONE => ()
        | SOME error => raise error
    end

  fun strategy_run_body Narrowing _ _ =
        raise Fail "narrowing is owned by Refute_QC_Narrow"
    | strategy_run_body strategy (config : Refute_Core.config)
      (instances : Refute_Core.instance list) =
    let
      (* Smart generators are the positive exhaustive CPS compilation.
         Random testing retains its existing generator/guard plans. *)
      val plan_config =
        if is_random strategy then
          Refute_Core.upd_smart_generators false config
        else config
      val cache = new_plan_cache ()
      val plans =
        (List.map (fn instance =>
           compile_plan_with cache plan_config (#goal instance)) instances
         handle error =>
           (if strategy = Exhaustive then
              ignore (Exn.capture clear_smart_gate_cache ())
            else ();
            raise error))
      val cached_selection =
        if strategy = Exhaustive then take_smart_gate_selection plans
        else NONE
      val _ =
        if not (Refute_Core.Private.enabled 3) then ()
        else List.app (fn (instance, plan) =>
          Refute_Core.Private.say 3
            ("Refute plan (card " ^ Int.toString (#card instance) ^
             "):\n" ^ pp_plan plan ^ "\n"))
          (ListPair.zip (instances, plans))
      val paired = ListPair.zip (instances, plans)
      val gated = List.exists (Option.isSome o #qc_gate) instances
      val original_gate_reasons = List.concat
        (List.mapPartial (fn (instance : Refute_Core.instance) =>
          #qc_gate instance) instances)
      val every_gated_plan_is_smart = List.all (fn (instance, plan) =>
        not (Option.isSome (#qc_gate instance)) orelse
        Refute_Eval.plan_uses_smart plan)
        paired
      val can_preflight = gated andalso strategy = Exhaustive andalso
        #smart_generators (#qc config) andalso every_gated_plan_is_smart
      val evals = List.concat
        (map (fn (instance : Refute_Core.instance) => #evals instance)
          instances)
      val smart_selection =
        case cached_selection of
            SOME selection => SOME selection
          | NONE =>
              if can_preflight then
                SOME (compile_smart_selected config true strategy plans evals)
              else NONE
      val preflight_reasons =
        case smart_selection of
            SOME (SelectionFailed reasons) => reasons
          | _ => []
      val gate_reasons =
        if not gated then []
        else if can_preflight andalso null preflight_reasons then []
        else original_gate_reasons @ preflight_reasons @
          (if can_preflight orelse is_random strategy then []
           else
             ["smart generators require an Enum-capable exhaustive substrate"])
      val selection =
        case smart_selection of
            SOME selected => selected
          | NONE => compile_selected config strategy (Plans plans)
    in
      (* [selection] may already hold a compiled test even when the gate
         reasons veto the run, so release it before reporting. *)
      if not (null gate_reasons) then
        (ignore (Exn.capture close_selection selection);
         Refute_Core.Unknown gate_reasons)
      else case selection of
          SelectionFailed reasons => Refute_Core.Unknown reasons
        | Selected (substrate, compiled) =>
            let
              fun selected_body () =
                let
                  val qc = #qc config
                  val cursor = schedule_cursor instances (#size qc)
                    (#size_mode qc)
                  val finite_schedule =
                    #size_mode qc = Refute_Core.FixedBound orelse
                    not (List.exists #size_matters instances)
              (* A random plan with no generators is exhaustive only after
                 there is an entry on which to run it.  In particular, zero
                 iterations and an empty instance set must not turn a
                 vacuous List.all into a proof of exhaustiveness. *)
              val complete = ref
                (Option.isSome (schedule_next cursor) andalso finite_schedule
                 andalso
                 (if is_random strategy then
                    bounded_size (#iterations (#qc config)) > 0 andalso
                    List.all (not o plan_has_gen) plans
                  else true))
              val counterexamples = ref []
              val replay_potential = ref NONE
              val discarded = ref 0
              val gave_up = ref []
              val frontier = ref (NONE : (int * int) option)
              val counters = new_counter_totals ()
              fun instance_for card = List.nth (instances, card - 1)
              fun stats_for size card msec =
                #decorate counters (!(#last_stats compiled)) @
                (if !discarded = 0 then []
                 else [("discarded", !discarded)]) @
                [("size", size), ("card", card), ("msec", msec)]
              fun one (card, size) draws genuine_only ignored retry_budget =
                let
                  val start = Time.now ()
                  (* Cleared before every call: a substrate whose [run]
                     leaves [last_stats] untouched on an exceptional exit
                     (a deadline, a compile-time handler) must read back
                     as "not measured this call", never the previous
                     call's numbers. *)
                  val _ = #last_stats compiled := []
                  val result = #run compiled
                    { genuine_only = genuine_only,
                      card = card,
                      size = size,
                      draws = draws,
                      ignored = ignored }
                  val msec = elapsed_msec start
                  val _ = #absorb counters (!(#last_stats compiled))
                in
                  case result of
                      Exhausted {complete = entry_complete} =>
                        complete := (!complete andalso entry_complete)
                    | GaveUp reason =>
                        (complete := false; add_reason reason gave_up)
                    | CexFound
                        {env, ground_env, case_tree, genuine, ...} =>
                        let
                          (* A candidate which needs replay or certification
                             is not evidence that this finite search was
                             exhaustive.  It may become a genuine result,
                             but if retries continue, NoCounterexample must
                             remain unavailable. *)
                          val _ = complete := false
                          val _ = record_candidate
                          { config = config,
                            strategy = strategy,
                            substrate = substrate,
                            instance = instance_for card,
                            stats = stats_for size card msec,
                            counterexamples = counterexamples,
                            discarded = discarded,
                            run_depth = NONE,
                            pnf_prefix = NONE,
                            (* Only replay failures accepted by the ordinary
                               keep-potential policy may enter the fallback;
                               genuine-only and continuing retries never do. *)
                            retain_replay_potential = fn potential =>
                              (replay_potential := SOME potential;
                               Refute_Core.publish_counterexamples
                                 [potential]),
                            retry = fn go => fn ig =>
                              (case retry_budget of
                                  NONE => one (card, size) draws go ig NONE
                                | SOME budget =>
                                    if !budget <= 0 then complete := false
                                    else
                                      (budget := !budget - 1;
                                       one (card, size) 1 go ig
                                         retry_budget)),
                            retry_potential = fn go => fn ig =>
                              (case retry_budget of
                                  NONE => one (card, size) draws go ig NONE
                                | SOME budget =>
                                    if !budget <= 0 then complete := false
                                    else
                                      (budget := !budget - 1;
                                       one (card, size) 1 go ig
                                         retry_budget)) }
                          { env = env,
                            ground_env = ground_env,
                            case_tree = case_tree,
                            genuine = genuine,
                            genuine_only = genuine_only,
                            ignored = ignored }
                          val _ = Refute_Core.publish_counterexamples
                            (rev (!counterexamples))
                        in
                          ()
                        end
                end
              fun run_entry entry =
                let
                  val started = Time.now ()
                  val total = bounded_size (#iterations (#qc config))
                  val target = Int.max (1, #max_counterexamples config)
                  (* Retries are random draws too.  Charge both initial
                     chunks and certification retries to this one budget. *)
                  val budget = ref total
                  fun chunks () =
                    if !budget <= 0 orelse
                       length (!counterexamples) >= target then ()
                    else
                      let
                        (* A substrate may stop after its first hit without
                           reporting how many draws it consumed.  Run one
                           draw at a time so a rejected hit leaves every
                           unused iteration available for certification. *)
                        val draws = 1
                        val _ = budget := !budget - draws
                        val reasons_before = length (!gave_up)
                        val _ = one entry draws (#genuine_only config) []
                          (SOME budget)
                      in
                        if length (!gave_up) > reasons_before then ()
                        else chunks ()
                      end
                  val _ =
                    if is_random strategy then chunks ()
                    else one entry 0 (#genuine_only config) [] NONE
                  val (card, size) = entry
                  val backend = strategy_name strategy
                  val elapsed = elapsed_msec started
                  val _ = Refute_Core.Private.say 2
                    ("Refute schedule entry (backend: " ^ backend ^
                     ", substrate: " ^ substrate ^ ", card " ^
                     Int.toString card ^ ", size " ^ Int.toString size ^
                     "): " ^ Int.toString elapsed ^ "ms\n")
                in
                  frontier := SOME entry
                end
              fun search current =
                if length (!counterexamples) >=
                     Int.max (1, #max_counterexamples config) orelse
                   Refute_Core.search_expired config then ()
                else
                  case schedule_next current of
                      NONE => ()
                    | SOME (entry, rest) =>
                        (run_entry entry; search rest)
              val _ = search cursor
              (* The frontier names the diagonally largest completed
                 schedule entry.  Type-variable cardinality only reaches
                 users when several monomorphic instances compete, and a
                 fixed-size search never reports its meaningless size. *)
              val frontier_reason =
                case !frontier of
                    NONE => []
                  | SOME (card, size) =>
                      let
                        val size_matters =
                          List.exists #size_matters instances
                        val poly = length instances > 1
                        val tyvar_part =
                          " (type variables of size " ^
                          Int.toString card ^ ")"
                      in
                        if size_matters then
                          ["searched up to size " ^ Int.toString size ^
                           (if poly then tyvar_part else "")]
                        else if poly then
                          ["searched type variables up to size " ^
                           Int.toString card]
                        else []
                      end
              val generic_reason =
                if is_random strategy then "random search exhausted"
                else "search space not exhausted"
              (* The vacuity signal: distinguishes a search that never
                 reached a Test node (every candidate failed its
                 premises) from one that genuinely exercised the
                 conclusion, without being a certainty decision itself.
                 Telemetry, not a search-inconclusive reason -- it rides
                 [Private.say] rather than the [Unknown] reason list, and
                 only when the outcome carries no witness: a found
                 counterexample already shows the counts via
                 [format_stats]. *)
              val counter_reason = #reason counters ()
            in
                  if not (null (!counterexamples)) then
                    Refute_Core.Counterexample (rev (!counterexamples))
                  else
                    case !replay_potential of
                        SOME potential =>
                          Refute_Core.Counterexample [potential]
                      | NONE =>
                          (Refute_Core.Private.say 1
                             (strategy_name strategy ^ ": " ^
                              counter_reason ^ "\n");
                           if !complete then Refute_Core.NoCounterexample
                           else Refute_Core.Unknown
                             (generic_reason :: !gave_up @ frontier_reason))
                end
              val body_result = Exn.capture selected_body ()
              val close_result = bounded_close (#close compiled)
            in
              case body_result of
                  Exn.Exn error =>
                    (ignore close_result; Exn.reraise error)
                  (* Surface a close failure even on a successful search,
                     then hand back the search's own outcome. *)
                | Exn.Res _ =>
                    (Exn.release close_result; Exn.release body_result)
            end
    end

  fun strategy_run strategy config instances =
    Refute_Core.with_search_context config
      (strategy_run_body strategy config) instances

  val exhaustive_backend : Refute_Core.backend =
    { name = "exhaustive",
      weight = 20,
      configured = fn () => true,
      (* Exhaustive SmartGen can discharge an ordinary executability gate
         by compiling every gated quantifier through an Enum substrate. *)
      requires = Refute_Core.ExecutableGoalUnless smart_gate_override,
      input = Refute_Core.MonoInstances,
      run = strategy_run Exhaustive }

  val random_backend : Refute_Core.backend =
    { name = "random",
      weight = 30,
      configured = fn () => true,
      requires = Refute_Core.ExecutableGoal,
      input = Refute_Core.MonoInstances,
      run = fn config =>
        strategy_run (Random {seed = strategy_seed config}) config }

  fun qc_backend_names () = ["exhaustive", "random", "narrowing"]

  fun register_backends () =
    (Refute_EvalSML.register_substrate
       {preflight = Refute_Extract.native_preflight,
        extract = Refute_Extract.extract_problem};
     Refute_EvalCompute.register_substrate ();
     Refute_EvalCv.register_substrate ();
     Refute_Core.register_backend exhaustive_backend;
     Refute_Core.register_backend random_backend;
     Refute_Core.register_run_release "qc-smart-gate-cache"
       clear_smart_gate_cache)

  val _ = register_backends ()
end
