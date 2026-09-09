structure ProofStepPlan :> ProofStepPlan =
struct

open TacticParse

datatype leaf_kind = TacticLeaf | ListTacticLeaf

datatype 'a selector =
    SelectFirst
  | SelectMatchingFirst of 'a
  | SelectMatchingAll of 'a

datatype select_mode = SelectSolve | SelectKeep

datatype 'a step =
    Leaf of {kind : leaf_kind, tactic : 'a tac_expr}
  | Each of 'a step list
  | Select of {selector : 'a selector, mode : select_mode,
               body : 'a step list}
  | Cases of 'a step list list
  | Choice of {source : 'a option, alternatives : 'a step list list}
  | Repeat of 'a step list
  | Try of 'a step list

type 'a plan = 'a step list

fun leaf kind tactic = Leaf {kind = kind, tactic = tactic}
fun tacticLeaf tactic = leaf TacticLeaf tactic
fun listLeaf tactic = leaf ListTacticLeaf tactic

fun stripGroup (Group (_, _, tactic)) = stripGroup tactic
  | stripGroup (RepairGroup (_, _, tactic, _)) = stripGroup tactic
  | stripGroup tactic = tactic

fun sourceAnnotation (Group (_, source, _)) = SOME source
  | sourceAnnotation (RepairGroup (source, _, _, _)) = SOME source
  | sourceAnnotation _ = NONE

(* A structured right-hand side of THEN has to run once for each goal made by
   its left-hand side.  Atomic tactics retain the usual THEN behaviour when an
   executor applies them to all focused goals, so they need no Each node. *)
fun needsEach tactic =
  case stripGroup tactic of
      Then tactics => List.exists needsEach tactics
    | ThenLT (_, [LReverse]) => false
    | ThenLT _ => true
    | By _ => true
    | SufficesBy _ => true
    | First _ => true
    | FirstProve _ => true
    | TacticParse.Try _ => true
    | _ => false

fun fromTactic tactic = planTactic tactic
and suffix tactic =
  if needsEach tactic then [Each (planTactic tactic)] else planTactic tactic
and planTactic tactic =
  case stripGroup tactic of
      Then [] => [tacticLeaf tactic]
    | Then (first :: rest) =>
        planTactic first @ List.concat (map suffix rest)
    (* Although TacticParse expands source-level REVERSE t to
       t THEN_LT REVERSE_LT, goal reordering is deliberately an atomic plan
       step.  Retaining tactic also retains its enclosing Group annotation. *)
    | ThenLT (_, [LReverse]) => [tacticLeaf tactic]
    | ThenLT (first, rest) =>
        planTactic first @ List.concat (map planListTactic rest)
    | By (quotation, body) =>
        [tacticLeaf (By (quotation, Then [])),
         Select {selector = SelectFirst, mode = SelectSolve,
                 body = planTactic body}]
    | SufficesBy (quotation, body) =>
        [tacticLeaf (SufficesBy (quotation, Then [])),
         Select {selector = SelectFirst, mode = SelectSolve,
                 body = planTactic body}]
    | First alternatives =>
        [Choice {source = sourceAnnotation tactic,
                 alternatives = map planTactic alternatives}]
    | FirstProve alternatives =>
        [Choice {source = sourceAnnotation tactic,
                 alternatives = map planTactic alternatives}]
    | TacticParse.Try body => [Try (planTactic body)]
    (* REPEAT recursively traverses every generated goal.  Until a plan
       executor records that traversal, splitting its body is unsound for
       failed-prefix resume. *)
    | TacticParse.Repeat _ => [tacticLeaf tactic]
    | _ => [tacticLeaf tactic]
and planListTactic tactic =
  case stripGroup tactic of
      LThenLT tactics => List.concat (map planListTactic tactics)
    | LThen (first, rest) =>
        planListTactic first @ List.concat (map suffix rest)
    | LThen1 body =>
        [Select {selector = SelectFirst, mode = SelectSolve,
                 body = planTactic body}]
    | LNullOk inner =>
        (case stripGroup inner of
             LTacsToLT (List (_, cases)) => Cases (map planTactic cases) :: nil
           | _ => [listLeaf tactic])
    (* List-tactic alternatives backtrack over a whole goal list.  Keep that
       traversal atomic; Choice models tactic alternatives on one goal. *)
    | LFirst _ => [listLeaf tactic]
    | LSelectGoal annotation =>
        [Select {selector = SelectMatchingFirst annotation,
                 mode = SelectKeep, body = []}]
    | LSelectGoals annotation =>
        [Select {selector = SelectMatchingAll annotation,
                 mode = SelectKeep, body = []}]
    | LSelectThen (selector, body) =>
        (case stripGroup selector of
             Rename annotation =>
               [Select {selector = SelectMatchingAll annotation,
                        mode = SelectSolve, body = planTactic body}]
           | _ => [listLeaf tactic])
    (* List-level try/repeat and goal-list reordering are kept atomic for the
       same reason as tactic-level REPEAT. *)
    | _ => [listLeaf tactic]

datatype path_component =
    PathStep of int
  | PathEach of int
  | PathSelect
  | PathCase of int
  | PathAlternative of int
  | PathTry
  | PathRepeat of int

type path = path_component list

fun nth 0 (x :: _) = SOME x
  | nth n (_ :: rest) = if n > 0 then nth (n - 1) rest else NONE
  | nth _ [] = NONE

fun stepAtPath plan target =
  let
    fun inPlan steps [PathStep i] = nth i steps
      | inPlan steps (PathStep i :: rest) =
          (case nth i steps of SOME step => inStep step rest | NONE => NONE)
      | inPlan _ _ = NONE
    and inStep step rest =
      case (step, rest) of
          (Each body, PathEach _ :: more) => inPlan body more
        | (Select {body, ...}, PathSelect :: more) => inPlan body more
        | (Cases cases, PathCase n :: more) =>
            if n > 0 then
              (case nth (n - 1) cases of
                   SOME body => inPlan body more
                 | NONE => NONE)
            else NONE
        | (Choice {alternatives, ...}, PathAlternative n :: more) =>
            if n > 0 then
              (case nth (n - 1) alternatives of
                   SOME body => inPlan body more
                 | NONE => NONE)
            else NONE
        | (Try body, PathTry :: more) => inPlan body more
        | (Repeat body, PathRepeat _ :: more) => inPlan body more
        | _ => NONE
  in
    inPlan plan target
  end

fun field text = Int.toString (size text) ^ ":" ^ text
fun node tag fields =
  field tag ^ field (Int.toString (length fields)) ^
  String.concat (map field fields)

fun kindText TacticLeaf = "tactic"
  | kindText ListTacticLeaf = "list-tactic"
fun modeText SelectSolve = "solve"
  | modeText SelectKeep = "keep"

fun canonicalPlan projections plan =
  let
    val {leaf = leafProjection, annotation} = projections
    fun selectorText SelectFirst = node "first" []
      | selectorText (SelectMatchingFirst value) =
          node "matching-first" [annotation value]
      | selectorText (SelectMatchingAll value) =
          node "matching-all" [annotation value]
    fun planText steps = node "plan" (map stepText steps)
    and stepText (Leaf {kind, tactic}) =
          node (kindText kind) [leafProjection kind tactic]
      | stepText (Each body) = node "each" [planText body]
      | stepText (Select {selector, mode, body}) =
          node "select" [selectorText selector, modeText mode, planText body]
      | stepText (Cases cases) =
          node "cases"
            [Int.toString (length cases),
             node "case-bodies" (map planText cases)]
      | stepText (Choice {alternatives, ...}) =
          node "choice"
            [Int.toString (length alternatives),
             node "alternative-bodies" (map planText alternatives)]
      | stepText (Repeat body) = node "repeat" [planText body]
      | stepText (Try body) = node "try" [planText body]
  in
    planText plan
  end

fun canonicalPrefix projections plan target =
  let
    val {leaf = leafProjection, annotation} = projections
    fun selectorText SelectFirst = node "first" []
      | selectorText (SelectMatchingFirst value) =
          node "matching-first" [annotation value]
      | selectorText (SelectMatchingAll value) =
          node "matching-all" [annotation value]
    fun fullPlan steps = canonicalPlan projections steps
    fun splitNth n xs =
      if n < 0 then NONE
      else
        let
          fun loop 0 prefix (x :: rest) = SOME (rev prefix, x, rest)
            | loop k prefix (x :: rest) = loop (k - 1) (x :: prefix) rest
            | loop _ _ [] = NONE
        in
          loop n [] xs
        end
    fun planPrefix steps path =
      case path of
          PathStep i :: rest =>
            (case splitNth i steps of
                 SOME (prior, step, _) =>
                   Option.map
                     (fn current => node "plan-prefix" [fullPlan prior, current])
                     (stepPrefix step rest)
               | NONE => NONE)
        | _ => NONE
    and stepPrefix step path =
      case (step, path) of
          (Leaf {kind, tactic}, []) =>
            SOME (node (kindText kind) [leafProjection kind tactic])
        | (Select {selector, mode, body}, PathSelect :: rest) =>
            Option.map
              (fn child => node "select-prefix"
                 [selectorText selector, modeText mode, child])
              (planPrefix body rest)
        | (Each body, PathEach iteration :: rest) =>
            if iteration < 0 then NONE
            else
              Option.map
                (fn child => node "each-prefix"
                   [Int.toString iteration,
                    if iteration = 0 then "" else fullPlan body,
                    child])
                (planPrefix body rest)
        | (Cases cases, PathCase n :: rest) =>
            if n <= 0 then NONE
            else
              (case splitNth (n - 1) cases of
                   SOME (prior, body, _) =>
                     Option.map
                       (fn child => node "cases-prefix"
                          [Int.toString (length cases),
                           node "completed-cases" (map fullPlan prior), child])
                       (planPrefix body rest)
                 | NONE => NONE)
        | (Choice {alternatives, ...}, PathAlternative n :: rest) =>
            if n <= 0 then NONE
            else
              (case splitNth (n - 1) alternatives of
                   SOME (prior, body, _) =>
                     Option.map
                       (fn child => node "choice-prefix"
                          [Int.toString (length alternatives),
                           node "attempted-alternatives" (map fullPlan prior),
                           child])
                       (planPrefix body rest)
                 | NONE => NONE)
        | (Try body, PathTry :: rest) =>
            Option.map (fn child => node "try-prefix" [child])
              (planPrefix body rest)
        | (Repeat body, PathRepeat iteration :: rest) =>
            if iteration < 0 then NONE
            else
              Option.map
                (fn child => node "repeat-prefix"
                   [Int.toString iteration,
                    if iteration = 0 then "" else fullPlan body,
                    child])
                (planPrefix body rest)
        | _ => NONE
  in
    planPrefix plan target
  end

end
