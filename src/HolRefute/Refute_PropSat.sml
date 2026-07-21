(*
 * Propositional formulas and the cdclite SAT solver.
 *
 * This is a HOL4 adaptation of Isabelle's prop_logic.ML and the cdclite
 * portion of sat_solver.ML, originally written by Tjark Weber
 * (Copyright 2004-2009).  The upstream code is distributed under the
 * BSD 3-Clause license.  HOL4 adaptation copyright 2026 The HOL4
 * contributors.
 *)

structure Refute_PropSat :> REFUTE_PROP_SAT = struct
  datatype prop_formula =
      True
    | False
    | BoolVar of int
    | Not of prop_formula
    | Or of prop_formula * prop_formula
    | And of prop_formula * prop_formula

  type assignment = int -> bool option
  datatype result =
      SATISFIABLE of assignment
    | UNSATISFIABLE

  exception INVALID_VARIABLE of int

  fun SNot True = False
    | SNot False = True
    | SNot (Not formula) = formula
    | SNot formula = Not formula

  fun SOr (True, _) = True
    | SOr (_, True) = True
    | SOr (False, formula) = formula
    | SOr (formula, False) = formula
    | SOr formulas = Or formulas

  fun SAnd (True, formula) = formula
    | SAnd (formula, True) = formula
    | SAnd (False, _) = False
    | SAnd (_, False) = False
    | SAnd formulas = And formulas

  fun simplify (Not formula) = SNot (simplify formula)
    | simplify (Or (left, right)) =
        SOr (simplify left, simplify right)
    | simplify (And (left, right)) =
        SAnd (simplify left, simplify right)
    | simplify formula = formula

  fun add_indices True values = values
    | add_indices False values = values
    | add_indices (BoolVar index) values = Lib.insert index values
    | add_indices (Not formula) values = add_indices formula values
    | add_indices (Or (left, right)) values =
        add_indices right (add_indices left values)
    | add_indices (And (left, right)) values =
        add_indices right (add_indices left values)

  fun indices formula = rev (add_indices formula [])

  fun validate formula =
    List.app
      (fn index =>
         if index > 0 then () else raise INVALID_VARIABLE index)
      (indices formula)

  fun maxidx True = 0
    | maxidx False = 0
    | maxidx (BoolVar index) = index
    | maxidx (Not formula) = maxidx formula
    | maxidx (Or (left, right)) =
        Int.max (maxidx left, maxidx right)
    | maxidx (And (left, right)) =
        Int.max (maxidx left, maxidx right)

  fun exists formulas =
    List.foldl (fn (formula, result) => SOr (result, formula))
      False formulas

  fun all formulas =
    List.foldl (fn (formula, result) => SAnd (result, formula))
      True formulas

  fun is_literal (BoolVar _) = true
    | is_literal (Not (BoolVar _)) = true
    | is_literal _ = false

  local
    fun is_conj_disj (Or (left, right)) =
          is_conj_disj left andalso is_conj_disj right
      | is_conj_disj (And (left, right)) =
          is_conj_disj left andalso is_conj_disj right
      | is_conj_disj formula = is_literal formula
  in
    fun is_nnf True = true
      | is_nnf False = true
      | is_nnf formula = is_conj_disj formula
  end

  local
    fun is_disjunction (Or (left, right)) =
          is_disjunction left andalso is_disjunction right
      | is_disjunction formula = is_literal formula

    fun is_conjunction (And (left, right)) =
          is_conjunction left andalso is_conjunction right
      | is_conjunction formula = is_disjunction formula
  in
    fun is_cnf True = true
      | is_cnf False = true
      | is_cnf formula = is_conjunction formula
  end

  fun nnf formula =
    let
      fun convert True = True
        | convert False = False
        | convert (BoolVar index) = BoolVar index
        | convert (Or (left, right)) =
            SOr (convert left, convert right)
        | convert (And (left, right)) =
            SAnd (convert left, convert right)
        | convert (Not True) = False
        | convert (Not False) = True
        | convert (Not (BoolVar index)) = Not (BoolVar index)
        | convert (Not (Or (left, right))) =
            SAnd (convert (SNot left), convert (SNot right))
        | convert (Not (And (left, right))) =
            SOr (convert (SNot left), convert (SNot right))
        | convert (Not (Not nested)) = convert nested
    in
      if is_nnf formula then formula else convert formula
    end

  fun defcnf formula =
    (validate formula;
     if is_cnf formula then formula
     else
      let
        val normalized = nnf formula
        val last_index = ref (maxidx normalized)

        fun fresh_index () =
          let
            val previous = !last_index
            val index =
              case Int.maxInt of
                  SOME maximum =>
                    if previous = maximum then
                      raise Fail
                        "Refute_PropSat.defcnf: no fresh variable index"
                    else previous + 1
                | NONE => previous + 1
          in
            last_index := index;
            index
          end

        fun define_or (And formulas) =
              let
                val index = fresh_index ()
                val variable = BoolVar index
              in
                (variable, [Or (Not variable, And formulas)])
              end
          | define_or (Or (left, right)) =
              let
                val (left', left_defs) = define_or left
                val (right', right_defs) = define_or right
              in
                (Or (left', right'), left_defs @ right_defs)
              end
          | define_or other = (other, [])

        fun convert True = True
          | convert False = False
          | convert (BoolVar index) = BoolVar index
          | convert (Not nested) = Not nested
          | convert (Or (BoolVar index, And (left, right))) =
              And (convert (Or (BoolVar index, left)),
                   convert (Or (BoolVar index, right)))
          | convert (Or (Not (BoolVar index), And (left, right))) =
              And (convert (Or (Not (BoolVar index), left)),
                   convert (Or (Not (BoolVar index), right)))
          | convert (Or (And (left, right), BoolVar index)) =
              And (convert (Or (left, BoolVar index)),
                   convert (Or (right, BoolVar index)))
          | convert (Or (And (left, right), Not (BoolVar index))) =
              And (convert (Or (left, Not (BoolVar index))),
                   convert (Or (right, Not (BoolVar index))))
          | convert (Or formulas) =
              let
                val (disjunction, definitions) =
                  define_or (Or formulas)
              in
                all (disjunction :: List.map convert definitions)
              end
          | convert (And (left, right)) =
              And (convert left, convert right)
    in
      convert normalized
    end)

  fun eval _ True = true
    | eval _ False = false
    | eval valuation (BoolVar index) = valuation index
    | eval valuation (Not formula) = not (eval valuation formula)
    | eval valuation (Or (left, right)) =
        eval valuation left orelse eval valuation right
    | eval valuation (And (left, right)) =
        eval valuation left andalso eval valuation right

  (* Integer-keyed maps back cdclite's variable, clause and proof tables.
     Redblackmap gives the logarithmic lookups and, crucially, the
     ascending-key fold order the decision heuristic relies on. *)
  type 'a int_table = (int, 'a) Redblackmap.dict

  fun empty_table () : 'a int_table = Redblackmap.mkDict Int.compare

  fun table_lookup key table = Redblackmap.peek (table, key)

  fun table_insert key value table = Redblackmap.insert (table, key, value)

  fun table_map_entry key function table =
    case Redblackmap.peek (table, key) of
        SOME value => Redblackmap.insert (table, key, function value)
      | NONE => raise Fail "Refute_PropSat: missing table entry"

  fun table_fold function table result =
    Redblackmap.foldl function result table

  fun table_cons key value table =
    table_insert key
      (value :: Option.getOpt (table_lookup key table, [])) table

  type clause = int list * int
  datatype reason = Decided | Implied of clause | Level0 of int
  type variable = bool option * reason * int * int
  type proofs = int * int list int_table
  type state =
    int * int list * variable int_table * clause list int_table * proofs

  exception CONFLICT of clause * state
  exception UNSAT of clause * state

  fun negate_literal literal = ~literal

  fun literal_value literal value =
    if literal > 0 then value else Option.map not value

  fun variable_of variables literal =
    case table_lookup (abs literal) variables of
        SOME variable => variable
      | NONE => raise Fail "Refute_PropSat: unknown variable"

  fun value_of variables literal =
    literal_value literal (#1 (variable_of variables literal))

  fun reason_of variables literal = #2 (variable_of variables literal)
  fun level_of variables literal = #3 (variable_of variables literal)

  fun is_true variables literal = value_of variables literal = SOME true
  fun is_false variables literal = value_of variables literal = SOME false
  fun is_unassigned variables literal = value_of variables literal = NONE

  fun assignment_of variables index =
    if index = 0 then NONE
    else
      case table_lookup (abs index) variables of
          NONE => NONE
        | SOME (value, _, _, _) => literal_value index value

  fun put_variable value reason level (_, _, _, rank) =
    (value, reason, level, rank)

  fun increment_rank (value, reason, level, rank) =
    (value, reason, level, rank + 1)

  fun update_variable literal function variables =
    table_map_entry (abs literal) function variables

  fun add_variable literal variables =
    table_insert (abs literal) (NONE, Decided, ~1, 0) variables

  fun assign literal reason level variables =
    update_variable literal
      (put_variable (SOME (literal > 0)) reason level) variables

  fun unassign literal variables =
    update_variable literal (put_variable NONE Decided ~1) variables

  fun add_proof [] (index, table) = (index, (index + 1, table))
    | add_proof premises (index, table) =
        (index, (index + 1, table_insert index premises table))

  fun level0_proof_of (Level0 index) = SOME index
    | level0_proof_of _ = NONE

  fun level0_proofs_of variables literals =
    List.mapPartial
      (fn literal => level0_proof_of (reason_of variables literal))
      literals

  fun premises_of variables (literals, proof) =
    proof :: level0_proofs_of variables literals

  fun make_proof variables clause proofs =
    add_proof (premises_of variables clause) proofs

  fun push literal clause (level, trail, variables, clauses, proofs) =
    let
      val (reason, proofs') =
        if level = 0 then
          let val (index, next_proofs) =
            make_proof variables clause proofs
          in (Level0 index, next_proofs) end
        else
          (Implied clause, proofs)
    in
      (level, literal :: trail,
       assign literal reason level variables, clauses, proofs')
    end

  fun push_decided literal
      (level, trail, variables, clauses, proofs) =
    (level + 1, literal :: 0 :: trail,
     assign literal Decided (level + 1) variables, clauses, proofs)

  fun propagate_clause (clause as (literals, _))
      (units, state as (level, _, variables, _, _)) =
    if List.exists (is_true variables) literals then
      (units, state)
    else if List.all (is_false variables) literals then
      if level = 0 then raise UNSAT (clause, state)
      else raise CONFLICT (clause, state)
    else
      case List.filter (is_unassigned variables) literals of
          [literal] =>
            (literal :: units, push literal clause state)
        | _ => (units, state)

  fun propagate units
      (state as (_, _, _, clauses, _)) =
    let
      fun propagate_unit (literal, context) =
        List.foldl
          (fn (clause, current) => propagate_clause clause current)
          context
          (Option.getOpt (table_lookup literal clauses, []))
    in
      case List.foldl propagate_unit ([], state) units of
          ([], state') => (NONE, state')
        | (units', state') => propagate units' state'
    end
    handle CONFLICT (clause, state') => (SOME clause, state')

  fun maximum_unassigned
      (variable, (NONE, _, _, rank), result as (_, best_rank)) =
        if rank > best_rank then (SOME variable, rank) else result
    | maximum_unassigned (_, _, result) = result

  fun decide (state as (_, _, variables, _, _)) =
    case table_fold maximum_unassigned variables (NONE, 0) of
        (SOME literal, _) => SOME (literal, push_decided literal state)
      | (NONE, _) => NONE

  fun mark literal marks = table_insert (abs literal) true marks

  fun marked marks literal =
    Option.getOpt (table_lookup (abs literal) marks, false)

  fun ignore_literal literal marks other =
    other = literal orelse marked marks other

  fun first_literal _ [] = raise List.Empty
    | first_literal _ (0 :: _) = raise List.Empty
    | first_literal predicate (literal :: literals) =
        if predicate literal then (literal, literals)
        else first_literal predicate literals

  fun reason_clause_of variables literal =
    case reason_of variables literal of
        Implied clause => clause
      | _ => raise Option.Option

  fun analyze conflicting_clause
      (level, trail, variables, _, _) =
    let
      fun back count literal (literals, proof) remaining_trail
          marks lower_literals proof_ids =
        let
          val (level0_literals, other_literals) =
            List.partition
              (fn item => level_of variables item = 0) literals
          val new_literals =
            List.filter
              (fn item => not (ignore_literal literal marks item))
              other_literals
          val lower =
            List.filter
              (fn item => level_of variables item <> level)
              new_literals
          val count' =
            length new_literals - length lower + count
          val marks' = List.foldl (fn (item, result) => mark item result)
            marks new_literals
          val lower_literals' = lower @ lower_literals
          val proof_ids' =
            level0_proofs_of variables level0_literals @
            (proof :: proof_ids)
          val (literal', trail') =
            first_literal (marked marks') remaining_trail
        in
          if count' = 1 then
            (negate_literal literal', lower_literals', rev proof_ids')
          else
            back (count' - 1) literal'
              (reason_clause_of variables literal') trail' marks'
              lower_literals' proof_ids'
        end
    in
      back 0 0 conflicting_clause trail (empty_table ()) [] []
    end

  fun keep_clause (clause as (literals, _))
      (level, trail, variables, clauses, proofs) =
    let
      val variables' =
        List.foldl
          (fn (literal, result) =>
             update_variable literal increment_rank result)
          variables literals
      val clauses' =
        List.foldl
          (fn (literal, result) =>
             table_cons (negate_literal literal) clause result)
          clauses literals
    in
      (level, trail, variables', clauses', proofs)
    end

  fun learn (clause as (literals, _)) state =
    if length literals <= 2 then keep_clause clause state else state

  fun backjump _ (state as (_, [], _, _, _)) = state
    | backjump count (level, 0 :: trail, variables, clauses, proofs) =
        let val state = (level - 1, trail, variables, clauses, proofs)
        in if count > 1 then backjump (count - 1) state else state end
    | backjump count
        (level, literal :: trail, variables, clauses, proofs) =
        backjump count
          (level, trail, unassign literal variables, clauses, proofs)

  fun maximum_level variables literals =
    List.foldl
      (fn (literal, result) =>
         Int.max (level_of variables literal, result))
      0 literals

  fun search units state =
    case propagate units state of
        (NONE, state' as (_, _, variables, _, _)) =>
          (case decide state' of
               NONE => SATISFIABLE (assignment_of variables)
             | SOME (literal, state'') => search [literal] state'')
      | (SOME conflicting_clause,
         state' as (level, trail, variables, clauses, proofs)) =>
          let
            val (literal, literals, premises) =
              analyze conflicting_clause state'
            val (index, proofs') = add_proof premises proofs
            val learned_clause = (literal :: literals, index)
            val jump = level - maximum_level variables literals
            val state'' =
              backjump jump
                (level, trail, variables, clauses, proofs')
            val state''' = learn learned_clause state''
            val state'''' = push literal learned_clause state'''
          in
            search [literal] state''''
          end

  fun has_opposing_literals [] = false
    | has_opposing_literals (literal :: literals) =
        List.exists (fn other => other = negate_literal literal) literals
        orelse has_opposing_literals literals

  fun add_clause (clause as ([_], _)) (units, state) =
        propagate_clause clause (units, state)
    | add_clause (clause as (literals, _)) context =
        if has_opposing_literals literals then context
        else
          let val (units, state) = context
          in (units, keep_clause clause state) end

  fun distinct_literals literals =
    rev (List.foldl (fn (literal, result) => Lib.insert literal result)
      [] literals)

  fun make_clauses literal_lists =
    let
      fun make [] proofs clauses = (rev clauses, proofs)
        | make (literals :: rest) proofs clauses =
            let
              val (index, proofs') = add_proof [] proofs
              val clause = (distinct_literals literals, index)
            in
              make rest proofs' (clause :: clauses)
            end
    in
      make literal_lists (0, empty_table ()) []
    end

  fun solve_clauses literal_lists =
    let
      val (clauses, proofs) = make_clauses literal_lists
      val variables =
        List.foldl
          (fn (literals, table) =>
             List.foldl
               (fn (literal, result) => add_variable literal result)
               table literals)
          (empty_table ()) literal_lists
      val state = (0, [], variables, empty_table (), proofs)
      val (units, state') =
        List.foldl
          (fn (clause, context) => add_clause clause context)
          ([], state) clauses
    in
      search units state'
    end
    handle UNSAT (conflicting_clause, (_, _, variables, _, proofs)) =>
      let val _ = make_proof variables conflicting_clause proofs
      in UNSATISFIABLE end

  fun formula_variable (BoolVar index) =
        if index > 0 then index else raise INVALID_VARIABLE index
    | formula_variable _ =
        raise Fail "Refute_PropSat: expected formula in CNF"

  fun literal_of (Not formula) = negate_literal (formula_variable formula)
    | literal_of formula = formula_variable formula

  fun clause_of (Or (left, right)) = clause_of left @ clause_of right
    | clause_of formula = [literal_of formula]

  fun clauses_of (And (left, right)) =
        clauses_of left @ clauses_of right
    | clauses_of True = [[1, ~1]]
    | clauses_of False = [[1], [~1]]
    | clauses_of formula = [clause_of formula]

  fun solve formula =
    (validate formula;
     let val cnf = if is_cnf formula then formula else defcnf formula
     in solve_clauses (clauses_of cnf) end)
end
