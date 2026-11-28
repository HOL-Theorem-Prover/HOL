(* ========================================================================= *)
(* FILE          : hhLamTrans.sml                                            *)
(* DESCRIPTION   : Lambda translations of the problem generator              *)
(* AUTHOR        : Lukasz Czajka                                             *)
(* ========================================================================= *)

structure hhLamTrans :> hhLamTrans =
struct

  open HolKernel boolSyntax

  fun fail message = raise Fail ("hhLamTrans: " ^ message)

  datatype mode = Lifting | Combs | CombsAndLifting | KeepLams

  val modes =
    [("lifting", Lifting), ("combs", Combs),
     ("combs_and_lifting", CombsAndLifting), ("keep_lams", KeepLams)]

  fun mode_of_string string =
    case List.find (fn (name, _) => name = string) modes of
        SOME (_, mode) => mode
      | NONE => fail ("unknown lambda mode " ^ String.toString string)

  fun mode_name mode = #1 (valOf (List.find (fn (_, m) => m = mode) modes))

  fun valid_mode string =
    List.exists (fn (name, _) => name = string) modes

  fun generated_symbol variable =
    let val name = #1 (dest_var variable) in
      String.isPrefix "pxy." name orelse String.isPrefix "$" name
    end

  fun close_formula tm =
    list_mk_forall (List.filter (not o generated_symbol) (free_vars_lr tm), tm)

  (* HOL represents binders as constants applied to abstractions.  Recognise
     that representation only in formula position.  In term position, as in
     p (!x. q x), the abstraction is an ordinary argument that lifting or
     combinator translation must remove. *)
  fun formula_map formula term tm =
    if is_forall tm then
      let val (var, body) = dest_forall tm in mk_forall (var, formula body) end
    else if is_exists tm then
      let val (var, body) = dest_exists tm in mk_exists (var, formula body) end
    else if is_neg tm then mk_neg (formula (dest_neg tm))
    else if is_conj tm then
      mk_conj (formula (lhand tm), formula (rand tm))
    else if is_disj tm then
      mk_disj (formula (lhand tm), formula (rand tm))
    else if is_imp_only tm then
      let
        val (left, right) = dest_imp tm
      in
        mk_imp (formula left, formula right)
      end
    else if is_eq tm andalso type_of (lhand tm) = Type.bool then
      mk_eq (formula (lhand tm), formula (rand tm))
    else term tm

  (* Do not open the combin theory: doing so changes the session grammar.
     Constants are looked up only by the combinator modes.  HOL4 calls the B
     combinator "o"; it has B's defining equation o f g x = f (g x). *)
  fun combin name =
    gen_tyvarify (prim_mk_const {Thy = "combin", Name = name})

  fun ucomb f x = mk_ucomb (f, x)

  fun apply2 f x y = ucomb (ucomb f x) y

  (* Instantiation of a polymorphic combinator is fixed by its final
     argument.  Peel that application back off to obtain the required
     function-valued combinator term. *)
  fun as_function variable tm = rator (ucomb tm variable)

  fun abstract variable tm =
    let
      (* Return whether the subtree contains [variable] together with its
         abstraction when it does, or the unchanged subtree when it does
         not.  This avoids the quadratic free-variable rescans of the direct
         textbook presentation on large premise sets. *)
      fun walk body =
        if aconv variable body then
          (true, as_function variable (combin "I"))
        else if is_comb body then
          let
            val left = rator body
            val right = rand body
            val (left_has, left') = walk left
            val (right_has, right') = walk right
          in
            if not left_has andalso right_has andalso
               aconv variable right then
              (true, left)
            else if left_has andalso right_has then
              (true, as_function variable
                (apply2 (combin "S") left' right'))
            else if left_has then
              (true, as_function variable
                (apply2 (combin "C") left' right))
            else if right_has then
              (true, as_function variable
                (apply2 (combin "o") left right'))
            else (false, body)
          end
        else (false, body)
      val (occurs, result) = walk tm
    in
      if occurs then result
      else as_function variable (ucomb (combin "K") tm)
    end

  fun eliminate_abs tm =
    let
      fun formula body = formula_map formula term body
      and term body =
        if is_abs body then
          let
            val (vars, matrix) = strip_abs body
            (* Once an abstraction itself is being combinatorized, every
               abstraction below it is a term-level function, including the
               representation lambda of a nested logical binder. *)
            val matrix' = term matrix
          in
            List.foldr (fn (var, result) => abstract var result) matrix' vars
          end
        else if is_comb body then
          mk_comb (term (rator body), term (rand body))
        else body
    in
      formula tm
    end

  fun eta_contract tm =
    let
      fun formula body = formula_map formula term body
      and term body =
        if is_abs body then
          let
            val (var, matrix) = dest_abs body
            val matrix' =
              if type_of matrix = Type.bool then formula matrix
              else term matrix
          in
            if is_comb matrix' andalso aconv (rand matrix') var andalso
               not (var_occurs var (rator matrix')) then term (rator matrix')
            else mk_abs (var, matrix')
          end
        else if is_comb body then
          mk_comb (term (rator body), term (rand body))
        else body
    in
      formula tm
    end

  fun lift formulas =
    let
      val next = ref 0
      val definitions = ref []

      fun fresh_name () =
        let
          val index = !next
          val _ = next := index + 1
        in
          "lam." ^ Int.toString index
        end

      fun formula tm = formula_map formula term tm
      and term tm =
        if is_abs tm then lift_abs tm
        else if is_comb tm then mk_comb (term (rator tm), term (rand tm))
        else tm
      and lift_abs tm =
        let
          val (bound, matrix) = strip_abs tm
          val captured = free_vars_lr tm
          (* A type variable occurring only inside the body would vanish
             from the symbol's type, so instances of the definition at
             different types would all define one symbol.  Pass it as a
             (:'b) argument to keep it in the type. *)
          val captured_type = list_mk_fun (map type_of captured, type_of tm)
          val visible = Type.type_vars captured_type
          val hidden =
            List.filter (fn ty => not (mem ty visible))
              (type_vars_in_term tm)
          val witnesses = map mk_itself hidden
          val arguments = witnesses @ captured
          val matrix' =
            if type_of matrix = Type.bool then formula matrix else term matrix
          val lam_type = list_mk_fun (map type_of witnesses, captured_type)
          val lam = mk_var (fresh_name (), lam_type)
          val replacement = list_mk_comb (lam, arguments)
          val _ = definitions :=
            {name = fst (dest_var lam), captured = captured, bound = bound,
             replacement = replacement, matrix = matrix'} :: !definitions
        in
          replacement
        end

      val rewritten = map (formula o close_formula) formulas
    in
      (rewritten, List.rev (!definitions))
    end

  fun lifted_definition {name, captured, bound, replacement, matrix} =
    (name, list_mk_forall (captured @ bound,
      mk_eq (list_mk_comb (replacement, bound), matrix)))

  (* Only the bound variables become combinators.  The captured ones stay
     quantified arguments of the lifted symbol: abstracting them too wraps
     the body in one more combinator layer per captured variable, so the
     definition grows quadratically in their number. *)
  fun combinator_definition {name, captured, bound, replacement, matrix} =
    (name ^ ".combs", eliminate_abs (list_mk_forall (captured,
      mk_eq (replacement, list_mk_abs (bound, matrix)))))

  fun translate Lifting formulas =
        let val (rewritten, definitions) = lift formulas in
          (rewritten, map lifted_definition definitions)
        end
    | translate Combs formulas =
        (map (eliminate_abs o close_formula) formulas, [])
    | translate CombsAndLifting formulas =
        let
          val (rewritten, definitions) = lift formulas
        in
          (rewritten, map lifted_definition definitions @
            map combinator_definition definitions)
        end
    | translate KeepLams formulas =
        (map (eta_contract o close_formula) formulas, [])

end
