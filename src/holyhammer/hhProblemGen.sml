structure hhProblemGen :> hhProblemGen =
struct

  open HolKernel boolSyntax

  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type
  type named_terms = {conjecture : term, facts : (string * term) list}
  type problem_options =
    {format : hhTptpProblem.format, type_enc : hhTypeEnc.type_enc,
     lam_trans : hhLamTrans.mode, mono_iters : int, mono_instances : int}

  datatype hol_formula =
      HQuant of bool * term list * hol_formula
    | HConn of hhTptpProblem.conn * hol_formula list
    | HAtom of term
  type formula_ir = {conjecture : hol_formula,
                     facts : (string * hol_formula) list}
  type proxy_ir = {conjecture : hol_formula,
                   facts : (string * hol_formula) list,
                   proxies : string list}

  datatype fo_term =
      FOHead of term * fo_term list
    | FOValue of term
    | FOApp of fo_app
    | FOPred of fo_term
    | FOAbs of term * fo_term
  withtype fo_app = {left : fo_term, right : fo_term,
                    function_type : hol_type, argument_type : hol_type,
                    result_type : hol_type}
  datatype fo_formula =
      FOQuant of bool * term list * fo_formula
    | FOConn of hhTptpProblem.conn * fo_formula list
    | FOAtom of fo_term
  type fo_ir = {conjecture : fo_formula, facts : (string * fo_formula) list,
                used_app : bool, used_pp : bool}

  fun fail message = raise Fail ("hhProblemGen: " ^ message)

  (* An abstraction that survives first-order lambda handling.  The text
     needs the grammar (Parse.term_to_string), so it is produced only by
     describe_failure, on the calling thread; the labels are the context
     prefixes ("fact NAME", "conjecture"), innermost first. *)
  exception Lambda_survived of string list * term

  fun describe_failure (Lambda_survived (labels, tm)) =
        let
          val base = "hhProblemGen: lambda survived first-order lambda " ^
            "handling: " ^ Parse.term_to_string tm
        in
          Fail (List.foldl (fn (label, message) =>
            "hhProblemGen: " ^ label ^ ": " ^ message) base labels)
        end
    | describe_failure exn = exn

  val syntax_of = hhTptpProblem.syntax_of

  fun is_full_ho (hhTptpProblem.THF _) = true
    | is_full_ho _ = false

  fun is_fool (hhTptpProblem.TFF {fool = hhTptpProblem.Fool _, ...}) = true
    | is_fool _ = false

  (* Whether [var] occurs free in [tm] at most once. *)
  fun occurs_at_most_once var tm =
    let
      fun count tm seen =
        if seen > 1 then seen
        else if is_var tm then if aconv tm var then seen + 1 else seen
        else if is_comb tm then count (rand tm) (count (rator tm) seen)
        else if is_abs tm then
          let val (bound, body) = dest_abs tm in
            if aconv bound var then seen else count body seen
          end
        else seen
    in
      count tm 0 <= 1
    end

  (* Unfolding LET (\v. body) arg copies arg into each occurrence of v, so
     a chain of lets that use their variable twice grows exponentially.
     Only a LET that copies nothing is unfolded; the others stay, and the
     LET_THM helper defines them. *)
  fun unfolds_without_copy func arg =
    is_var arg orelse is_const arg orelse
    uncurry occurs_at_most_once (dest_abs func)

  (* This is deliberately a term operation rather than a simplifier: the
     generator must retain non-$ite COND for the helper facts. *)
  fun beta_eta_contract unfold_let tm =
    let
      fun recurse body =
        if is_abs body then
          let
            val (var, matrix) = dest_abs body
            val matrix' = recurse matrix
          in
            if is_comb matrix' andalso aconv (rand matrix') var andalso
               not (var_occurs var (rator matrix')) then
              recurse (rator matrix')
            else mk_abs (var, matrix')
          end
        else if unfold_let andalso is_let body andalso
                is_abs (fst (dest_let body)) then
          (* Judged after contraction: contracting the function can make
             its variable occur more often
             (let x = a in let y = x in g y y). *)
          let
            val (func, arg) = dest_let body
            val func' = recurse func
            val arg' = recurse arg
          in
            if not (is_abs func') then mk_comb (func', arg')
            else if unfolds_without_copy func' arg' then
              recurse (beta_conv (mk_comb (func', arg')))
            else mk_comb (mk_comb (rator (rator body), func'), arg')
          end
        else if is_comb body then
          let
            val left = recurse (rator body)
            val right = recurse (rand body)
            val combined = mk_comb (left, right)
          in
            if is_abs left then recurse (beta_conv combined) else combined
          end
        else body
    in
      recurse tm
    end

  fun presimp _ ({conjecture, facts} : named_terms) =
    let
      (* LET is unfolded even for formats with $let: the generator does not
         emit $let, so a kept LET reaches the prover as a constant, which
         hol_helpers defines with LET_THM. *)
      val simplify = beta_eta_contract true
    in
      {conjecture = simplify conjecture,
       facts = map (fn (name, tm) => (name, simplify tm)) facts}
    end

  fun effective_mode format mode =
    if mode = hhLamTrans.KeepLams andalso not (is_full_ho format) then
      hhLamTrans.Lifting
    else mode

  (* The passes that draw fresh names take their supply (hhNames) as the
     first argument; the public passes take the global counter. *)
  fun lambda_with names format mode ({conjecture, facts} : named_terms) =
    let
      val mode' = effective_mode format mode
      val formulas = conjecture :: map #2 facts
      val (rewritten, definitions) =
        hhLamTrans.translate_with names mode' formulas
    in
      {conjecture = hd rewritten,
       facts = ListPair.zip (map #1 facts, tl rewritten) @ definitions}
    end

  val pass_lambda = lambda_with hhNames.global

  fun is_monomorphic (hhTypeEnc.Native {poly = false, ...}) = true
    | is_monomorphic (hhTypeEnc.Guards {poly = false, ...}) = true
    | is_monomorphic _ = false

  fun monomorph_with names encoding caps ({conjecture, facts} : named_terms) =
    if is_monomorphic encoding then
      {conjecture = conjecture,
       facts = hhMonomorph.monomorph_pool caps
                 (hhMonomorph.mk_pool_with names conjecture) facts}
    else {conjecture = conjecture, facts = facts}

  val pass_monomorph = monomorph_with hhNames.global

  (* Monomorphization against a reusable ground pool (the goal's). *)
  fun pass_monomorph_pool encoding caps pool facts =
    if is_monomorphic encoding then
      hhMonomorph.monomorph_pool caps pool facts
    else facts

  fun skeleton tm =
    if is_forall tm then
      let val (var, body) = dest_forall tm in
        HQuant (true, [var], skeleton body)
      end
    else if is_exists tm then
      let val (var, body) = dest_exists tm in
        HQuant (false, [var], skeleton body)
      end
    else if is_neg tm then HConn (hhTptpProblem.Not, [skeleton (dest_neg tm)])
    else if is_conj tm then
      HConn (hhTptpProblem.And, [skeleton (lhand tm), skeleton (rand tm)])
    else if is_disj tm then
      HConn (hhTptpProblem.Or, [skeleton (lhand tm), skeleton (rand tm)])
    else if is_imp_only tm then
      let val (left, right) = dest_imp tm in
        HConn (hhTptpProblem.Implies, [skeleton left, skeleton right])
      end
    else if is_eq tm andalso type_of (lhand tm) = Type.bool then
      HConn (hhTptpProblem.Iff, [skeleton (lhand tm), skeleton (rand tm)])
    else HAtom tm

  fun formula_skeleton ({conjecture, facts} : named_terms) =
    {conjecture = skeleton conjecture,
     facts = map (fn (name, tm) => (name, skeleton tm)) facts}

  fun logical_info head =
    if same_const head negation then SOME ("not", 1, "$not")
    else if same_const head conjunction then SOME ("conj", 2, "$and")
    else if same_const head disjunction then SOME ("disj", 2, "$or")
    else if same_const head implication then SOME ("imp", 2, "$implies")
    else if same_const head equality then SOME ("eq", 2, "$equal")
    else if same_const head universal then SOME ("all", 1, "$forall")
    else if same_const head existential then SOME ("ex", 1, "$exists")
    else if same_const head T then SOME ("true", 0, "$true")
    else if same_const head F then SOME ("false", 0, "$false")
    else NONE

  fun rebuild head args = list_mk_comb (head, args)
  fun proxy_head name head = mk_var ("pxy." ^ name, type_of head)
  fun builtin_head name head = mk_var (name, type_of head)
  fun is_cond_head head = same_const head conditional

  fun transform_term format record tm =
    let
      val (head, args) = strip_comb tm
      val args' = map (transform_term format record) args
      val argc = length args
      val {with_ite, ...} = syntax_of format
      fun use_proxy name =
        (record name; rebuild (proxy_head name head) args')
      fun use_builtin name = rebuild (builtin_head name head) args'
    in
      if is_cond_head head andalso with_ite andalso argc >= 3 then
        use_builtin "$ite"
      else
        case logical_info head of
            NONE =>
              if is_abs tm then
                let val (var, body) = dest_abs tm in
                  mk_abs (var, transform_term format record body)
                end
              else if null args then head
              else rebuild (transform_term format record head) args'
          | SOME (name, card, builtin) =>
              if (name = "true" orelse name = "false") andalso
                 (is_full_ho format orelse is_fool format) then
                use_builtin builtin
              else use_proxy name
    end

  (* The proxy transformation of one formula.  [record] is called with
     the name of each proxy as it is introduced. *)
  fun proxy_formula format record =
    let
      val transform = transform_term format record
      (* An equation in formula position is TPTP equality.  Only equations
         below other symbols need the pxy.eq proxy. *)
      fun atom tm =
        if is_eq tm then
          let val (left, right) = dest_eq tm in
            list_mk_comb (builtin_head "$equal" (rator (rator tm)),
              [transform left, transform right])
          end
        else transform tm
      fun formula (HQuant (all, vars, body)) = HQuant (all, vars, formula body)
        | formula (HConn (conn, bodies)) = HConn (conn, map formula bodies)
        | formula (HAtom tm) = HAtom (atom tm)
    in
      formula
    end

  fun introduce_proxies format ({conjecture, facts} : formula_ir) =
    let
      val seen = ref []
      fun record name =
        if List.exists (fn old => old = name) (!seen) then ()
        else seen := !seen @ [name]
      val formula = proxy_formula format record
      val conjecture' = formula conjecture
      val facts' = map (fn (name, body) => (name, formula body)) facts
    in
      {conjecture = conjecture', facts = facts', proxies = !seen}
    end

  fun translate_front {format, type_enc, lam_trans, mono_iters,
                       mono_instances} terms =
    introduce_proxies format
      (formula_skeleton
        (pass_monomorph type_enc
          {max_iters = mono_iters, max_new_instances = mono_instances}
          (pass_lambda format lam_trans (presimp format terms))))

  fun type_is_fun ty =
    (ignore (Type.dom_rng ty); true) handle HOL_ERR _ => false
  fun dom_rng ty = SOME (Type.dom_rng ty) handle HOL_ERR _ => NONE

  fun term_head tm = fst (strip_comb tm)
  fun is_generated_var tm =
    is_var tm andalso
    let val name = fst (dest_var tm) in
      String.isPrefix "pxy." name orelse String.isPrefix "$" name orelse
      String.isPrefix "lam." name
    end
  fun is_symbol tm = is_const tm orelse is_generated_var tm

  (* Heads are constants or variables, for which Term.compare is EQUAL
     exactly when they are aconv. *)
  val same_head = aconv

  (* Lists of first occurrences, in occurrence order. *)
  fun distinct_heads heads = aiLib.mk_sameorder_set Term.compare heads

  fun add_head head arity table =
    if not (is_symbol head) then table
    else
      case Redblackmap.peek (table, head) of
          SOME (min, max) =>
            if arity < min then Redblackmap.insert (table, head, (arity, max))
            else if arity > max then
              Redblackmap.insert (table, head, (min, arity))
            else table
        | NONE => Redblackmap.insert (table, head, (arity, arity))

  fun heads_of_term tm table =
    let val (head, args) = strip_comb tm in
      List.foldl (fn (arg, result) => heads_of_term arg result)
        (add_head head (length args) table) args
    end

  fun heads_of_formula (HQuant (_, _, body)) table = heads_of_formula body table
    | heads_of_formula (HConn (_, bodies)) table =
        List.foldl (fn (body, result) => heads_of_formula body result)
          table bodies
    | heads_of_formula (HAtom tm) table = heads_of_term tm table

  fun vars_of_formula (HQuant (_, vars, body)) result =
        vars_of_formula body
          (List.filter (not o is_generated_var) vars @ result)
    | vars_of_formula (HConn (_, bodies)) result =
        List.foldl (fn (body, acc) => vars_of_formula body acc) result bodies
    | vars_of_formula (HAtom _) result = result

  fun min_arity var_types (head, (ordinary, _)) =
    let
      fun lower count best ty =
        if count >= ordinary then best
        else
          case dom_rng ty of
              NONE => best
            | SOME (_, range) =>
                lower (count + 1)
                  (if Redblackset.member (var_types, ty) then count else best)
                  range
    in
      lower 0 ordinary (type_of head)
    end

  (* Pass 6.  Sufficient_App_Op retains direct applications unless a
     function-typed variable can consume a partial result.  Isabelle's
     45-fact poly-native cut-over uses Min_App_Op: direct symbols then keep
     their largest observed spine, trading a few partial applications for a
     smaller declaration/application vocabulary. *)
  fun app_arities encoding nfacts variables table =
    if (case encoding of
            hhTypeEnc.Native {poly = true, ...} => nfacts >= 45
          | _ => false) then
      Redblackmap.map (fn (_, (_, max)) => max) table
    else
      let
        val var_types = Redblackset.addList
          (Redblackset.empty Type.compare, map type_of (variables ()))
      in
        Redblackmap.map (min_arity var_types) table
      end

  fun arity_for head arities =
    case Redblackmap.peek (arities, head) of SOME arity => arity | NONE => 0

  fun firstorderize format encoding ({conjecture, facts} : formula_ir) =
    if is_full_ho format then
      let
        fun term in_position tm =
          if is_abs tm then
            let val (var, body) = dest_abs tm in
              FOAbs (var, term false body)
            end
          else
            let val (head, args) = strip_comb tm in
              FOHead (head, map (term true) args)
            end
        fun formula (HQuant (all, vars, body)) =
              FOQuant (all, vars, formula body)
          | formula (HConn (conn, bodies)) = FOConn (conn, map formula bodies)
          | formula (HAtom tm) = FOAtom (term false tm)
      in
        {conjecture = formula conjecture,
         facts = map (fn (name, body) => (name, formula body)) facts,
         used_app = false, used_pp = false}
      end
    else
      let
        val table = heads_of_formula conjecture
          (List.foldl
            (fn ((_, formula), result) =>
              heads_of_formula formula result)
            (Redblackmap.mkDict Term.compare) facts)
        fun variables () = vars_of_formula conjecture
          (List.foldl
            (fn ((_, formula), result) =>
              vars_of_formula formula result)
            [] facts)
        val arities = app_arities encoding (length facts) variables table
        val used_app = ref false
        val used_pp = ref false
        fun term in_position tm =
          if is_abs tm then
            raise Lambda_survived ([], tm)
          else
            let
              val (head, args) = strip_comb tm
              val minimum =
                if is_var head andalso #1 (dest_var head) = "$equal" then 2
                else if is_var head andalso #1 (dest_var head) = "$ite" then 3
                else if is_symbol head then arity_for head arities else 0
              val direct_arity = if length args < minimum then 0 else minimum
              val direct_args = List.take (args, direct_arity)
              val head_type = type_of head
              val direct =
                if direct_arity = 0 andalso type_is_fun head_type then
                  FOValue head
                else FOHead (head, map (term true) direct_args)
              (* The HOL spine is already checked.  Follow its function
                 ranges instead of rebuilding and retyping each prefix. *)
              val direct_type = List.foldl
                (fn (_, ty) => #2 (Type.dom_rng ty)) head_type direct_args
              val (applied, final_type) = List.foldl
                (fn (arg, (result, function_type)) =>
                let
                  val (argument_type, result_type) = Type.dom_rng function_type
                in
                  used_app := true;
                  (FOApp {left = result, right = term true arg,
                          function_type = function_type,
                          argument_type = argument_type,
                          result_type = result_type}, result_type)
                end) (direct, direct_type) (List.drop (args, direct_arity))
              val boolean = final_type = Type.bool
              val equation =
                is_var head andalso #1 (dest_var head) = "$equal"
            in
              (* Without FOOL a Boolean is a term of the bool sort, so a
                 formula atom reads it through pp. *)
              if not in_position andalso boolean andalso not equation andalso
                 not (is_fool format) then
                (used_pp := true; FOPred applied)
              else applied
            end
        fun formula (HQuant (all, vars, body)) =
              FOQuant (all, vars, formula body)
          | formula (HConn (conn, bodies)) = FOConn (conn, map formula bodies)
          | formula (HAtom tm) = FOAtom (term false tm)
        fun named_formula (name, body) =
          (name, formula body)
          handle Fail message => fail ("fact " ^ name ^ ": " ^ message)
               | Lambda_survived (labels, tm) =>
                   raise Lambda_survived (labels @ ["fact " ^ name], tm)
        val conjecture' = formula conjecture
          handle Fail message => fail ("conjecture: " ^ message)
               | Lambda_survived (labels, tm) =>
                   raise Lambda_survived (labels @ ["conjecture"], tm)
      in
        {conjecture = conjecture',
         facts = map named_formula facts,
         used_app = !used_app, used_pp = !used_pp}
      end

  fun add_once equal value values =
    if List.exists (equal value) values then values else values @ [value]
  fun same_value left right = left = right
  (* Distinct types in first-occurrence order.  The state is a membership
     set and the reversed list of first occurrences; types of one formula
     are visited in occurrence order, nested arguments after their type.
     Skipping a seen type together with its arguments is sound: a type's
     arguments are always added when the type is. *)
  fun add_type ty (seen, firsts) =
    if Redblackmap.inDomain (seen, ty) then (seen, firsts)
    else
      let
        val state = (Redblackmap.insert (seen, ty, ()), ty :: firsts)
      in
        if is_vartype ty then state
        else List.foldl (fn (arg, st) => add_type arg st) state
               (#Args (Type.dest_thy_type ty))
      end
  fun add_formula_types (FOQuant (_, vars, body)) state =
        add_formula_types body
          (List.foldl (fn (var, st) => add_type (type_of var) st) state vars)
    | add_formula_types (FOConn (_, bodies)) state =
        List.foldl (fn (body, st) => add_formula_types body st) state bodies
    | add_formula_types (FOAtom tm) state = add_fo_term_types tm state
  and add_fo_term_types (FOHead (head, args)) state =
        List.foldl (fn (arg, st) => add_fo_term_types arg st)
          (add_type (type_of head) state) args
    | add_fo_term_types (FOValue head) state = add_type (type_of head) state
    | add_fo_term_types (FOApp {left, right, function_type, argument_type,
                                result_type}) state =
        add_fo_term_types right (add_fo_term_types left
          (add_type result_type (add_type argument_type
            (add_type function_type state))))
    | add_fo_term_types (FOPred body) state = add_fo_term_types body state
    | add_fo_term_types (FOAbs (var, body)) state =
        add_fo_term_types body (add_type (type_of var) state)

  (* Same as distinct_types of the occurrences of all the formulas, the
     last formula's types first. *)
  fun distinct_formula_types formulas =
    rev (#2 (List.foldr (fn (formula, state) =>
      add_formula_types formula state)
      (Redblackmap.mkDict Type.compare, []) formulas))

  fun raw_mangle_type ty =
    if is_vartype ty then "var." ^ dest_vartype ty
    else
      let val {Thy, Tyop, Args} = Type.dest_thy_type ty in
        Thy ^ "." ^ Tyop ^
        (if null Args then "" else "(" ^
          String.concatWith "," (map raw_mangle_type Args) ^ ")")
      end

  (* A mangled name spells out whole types, so nested types make it
     arbitrarily long, and it is printed at every use.  A name over 80
     characters keeps a readable prefix and ends in a hash of the whole
     name, as app_symbol does. *)
  fun bounded_name name =
    if size name <= 80 then name
    else String.substring (name, 0, 48) ^ "_" ^
      String.substring (aiLib.sha1_string name, 0, 16)

  fun mangle_type ty =
    bounded_name (aiLib.escape ("ty." ^ raw_mangle_type ty))

  fun native_type ty =
    if is_vartype ty then
      hhTptpProblem.TyVar ("A" ^ aiLib.escape (dest_vartype ty))
    else
      let
        val {Thy, Tyop, Args} = Type.dest_thy_type ty
      in
        if Thy = "min" andalso Tyop = "fun" then
          (case Args of
             [domain, range] => hhTptpProblem.TyFun (native_type domain,
               native_type range)
           | _ => fail "malformed function type")
        else if Thy = "min" andalso Tyop = "bool" then
          hhTptpProblem.TyCon ("$o", [])
        else hhTptpProblem.TyCon
          (aiLib.escape ("ty." ^ Thy ^ "." ^ Tyop), map native_type Args)
      end

  fun mono_higher_type ty =
    if is_vartype ty then hhTptpProblem.TyCon (mangle_type ty, [])
    else
      let val {Thy, Tyop, Args} = Type.dest_thy_type ty in
        if Thy = "min" andalso Tyop = "fun" then
          (case Args of
               [domain, range] => hhTptpProblem.TyFun
                 (mono_higher_type domain, mono_higher_type range)
             | _ => fail "malformed function type")
        else if Thy = "min" andalso Tyop = "bool" then
          hhTptpProblem.TyCon ("$o", [])
        else hhTptpProblem.TyCon (mangle_type ty, [])
      end

  fun type_for (hhTypeEnc.Native {poly = true, ...}) = native_type
    | type_for (hhTypeEnc.Native {higher = true, ...}) = mono_higher_type
    | type_for (hhTypeEnc.Native {fool = true, ...}) = (fn ty =>
        if ty = Type.bool then hhTptpProblem.TyCon ("$o", [])
        else hhTptpProblem.TyCon (mangle_type ty, []))
    | type_for _ = fn ty => hhTptpProblem.TyCon (mangle_type ty, [])

  fun const_type_args tm =
    if not (is_const tm) then []
    else
      let
        val {Thy, Name, Ty} = dest_thy_const tm
        val generic = type_of (prim_mk_const {Thy = Thy, Name = Name})
        val (subst, unmatched) = raw_match_type generic Ty ([], [])
        fun image variable =
          case List.find (fn entry => #redex entry = variable) subst of
              SOME entry => #residue entry
            | NONE => variable
      in
        map image (Type.type_vars generic)
      end

  fun raw_symbol head =
    if is_const head then
      let val {Thy, Name, ...} = dest_thy_const head in
        "c." ^ Thy ^ "." ^ Name
      end
    else if is_var head then fst (dest_var head)
    else fail "term head is neither a constant nor a variable"

  fun variable_name name =
    if size name > 0 andalso Char.isUpper (String.sub (name, 0)) then
      aiLib.escape name
    else "V_" ^ aiLib.escape name

  fun proxy_type_args head =
    let
      val name = raw_symbol head
      val args = #1 (strip_fun (type_of head))
    in
      case name of
          "pxy.eq" => (case args of ty :: _ => [ty] | [] => [])
        | "pxy.all" =>
            (case args of ty :: _ =>
              (case dom_rng ty of SOME (domain, _) => [domain] | NONE => [])
             | [] => [])
        | "pxy.ex" =>
            (case args of ty :: _ =>
              (case dom_rng ty of SOME (domain, _) => [domain] | NONE => [])
             | [] => [])
        | "$ite" => (case args of _ :: ty :: _ => [ty] | _ => [])
        | _ => []
    end

  fun type_args_of_head head =
    if is_const head then const_type_args head
    else if is_generated_var head then proxy_type_args head
    else []

  fun is_lambda_var head =
    is_var head andalso String.isPrefix "lam." (fst (dest_var head))

  (* Lambda lifting runs before monomorphization, so a lifted lam.<n> can
     be polymorphic and reach the mono printer at several ground types.
     Being a variable, it has no generic type to match against: its whole
     type names the instance, as type arguments do for constants. *)
  fun mono_type_args head =
    if is_lambda_var head then [type_of head] else type_args_of_head head

  fun encoded_symbol encoding head =
    if is_var head andalso not (is_generated_var head) then
      variable_name (raw_symbol head)
    else if raw_symbol head = "$true" orelse raw_symbol head = "$false" orelse
            raw_symbol head = "$equal" then raw_symbol head
    else
      case encoding of
          hhTypeEnc.Native {poly = true, ...} =>
            aiLib.escape (if raw_symbol head = "$ite" then "pxy.ite"
                          else raw_symbol head)
        | _ =>
            let
              val args = mono_type_args head
              val base = if raw_symbol head = "$ite" then "pxy.ite"
                         else raw_symbol head
            in
              if null args then aiLib.escape base
              else bounded_name (aiLib.escape (base ^ "." ^
                String.concatWith "." (map raw_mangle_type args)))
            end

  fun app_symbol (hhTypeEnc.Native {poly = false, ...})
        (function_type, argument_type, result_type) =
        "app_" ^ String.substring (aiLib.sha1_string
          (raw_mangle_type function_type ^ "\n" ^
           raw_mangle_type argument_type ^ "\n" ^
           raw_mangle_type result_type), 0, 16)
    | app_symbol _ _ = "app_2E"

  fun is_bound_var head = is_var head andalso not (is_generated_var head)

  (* A bound variable stays the TPTP variable its quantifier binds. *)
  fun value_symbol (encoding as hhTypeEnc.Native {poly = false, ...}) head =
        if is_bound_var head then encoded_symbol encoding head else
        "value_" ^ aiLib.escape (raw_symbol head) ^ "_" ^
        String.substring
          (aiLib.sha1_string (raw_mangle_type (type_of head)), 0, 12)
    | value_symbol encoding head = encoded_symbol encoding head

  fun signature_compare ((f, a, r), (f', a', r')) =
    case Type.compare (f, f') of
        EQUAL =>
          (case Type.compare (a, a') of
               EQUAL => Type.compare (r, r')
             | order => order)
      | order => order

  (* Per-problem memo of the symbols above, shared by declarations, guard
     axioms and formula encoding.  Entries are computed on demand; a bound
     variable keeps its direct, uncached path. *)
  type symbols =
    {head : term -> string, value : term -> string,
     type_args : term -> hhTptpProblem.tptp_type list,
     app : hol_type * hol_type * hol_type -> string}

  fun memoise compare f =
    let
      val table = ref (Redblackmap.mkDict compare)
    in
      fn key =>
        case Redblackmap.peek (!table, key) of
            SOME result => result
          | NONE =>
              let val result = f key in
                table := Redblackmap.insert (!table, key, result); result
              end
    end

  fun symbol_table encoding : symbols =
    let
      val head = memoise Term.compare (encoded_symbol encoding)
      val value = memoise Term.compare (value_symbol encoding)
      val type_args =
        case encoding of
            hhTypeEnc.Native {poly = true, ...} =>
              let val args = memoise Term.compare
                  (map native_type o type_args_of_head)
              in fn tm => if is_bound_var tm then [] else args tm end
          | _ => fn _ => []
      fun unless_bound memo tm =
        if is_bound_var tm then encoded_symbol encoding tm else memo tm
    in
      {head = unless_bound head, value = unless_bound value,
       type_args = type_args,
       app = memoise signature_compare (app_symbol encoding)}
    end

  fun encode_term (symbols : symbols) encoding (FOHead (head, args)) =
        hhTptpProblem.Tm (((if is_var head andalso raw_symbol head = "$ite"
          andalso length args = 3 then "$ite" else #head symbols head),
          #type_args symbols head), map (encode_term symbols encoding) args)
    | encode_term symbols _ (FOValue head) =
        hhTptpProblem.Tm ((#value symbols head, []), [])
    | encode_term symbols encoding (FOApp {left, right, function_type,
                                           argument_type, result_type}) =
        hhTptpProblem.Tm ((#app symbols
          (function_type, argument_type, result_type), []),
          [encode_term symbols encoding left,
           encode_term symbols encoding right])
    | encode_term symbols encoding (FOPred body) =
        hhTptpProblem.Tm (("pp_2E", []),
          [encode_term symbols encoding body])
    | encode_term symbols encoding (FOAbs (var, body)) =
        hhTptpProblem.TmAbs ((variable_name (fst (dest_var var)),
          type_for encoding (type_of var)),
          encode_term symbols encoding body)

  fun type_vars_of_formula formula =
    let
      fun collect_ty ty result =
        if is_vartype ty then add_once same_value ty result
        else let val {Args, ...} = Type.dest_thy_type ty in
          List.foldl (fn (arg, acc) => collect_ty arg acc) result Args
        end
      fun collect_term (FOHead (head, args)) result =
            List.foldl (fn (arg, acc) => collect_term arg acc)
              (collect_ty (type_of head) result) args
        | collect_term (FOValue head) result =
            collect_ty (type_of head) result
        | collect_term (FOApp {left, right, ...}) result =
            collect_term right (collect_term left result)
        | collect_term (FOPred body) result = collect_term body result
        | collect_term (FOAbs (var, body)) result =
            collect_term body (collect_ty (type_of var) result)
      fun collect (FOQuant (_, vars, body)) result =
            collect body (List.foldl (fn (var, acc) =>
              collect_ty (type_of var) acc) result vars)
        | collect (FOConn (_, bodies)) result =
            List.foldl (fn (body, acc) => collect body acc) result bodies
        | collect (FOAtom tm) result = collect_term tm result
    in
      collect formula []
    end

  fun guard_name ty = aiLib.escape ("gd." ^ mangle_type ty)
  fun guard_atom ty tm =
    hhTptpProblem.Atom (hhTptpProblem.Tm ((guard_name ty, []), [tm]))

  fun guarded_type
      (hhTypeEnc.Guards {level = hhTypeEnc.AllTypes, ...}) _ _ = true
    | guarded_type (hhTypeEnc.Guards {level = hhTypeEnc.NonmonoNonUniform, ...})
        needs ty = List.exists (fn other => other = ty) needs
    | guarded_type _ _ _ = false

  (* Pass 8 soundness argument.  Mangled native symbols interpret every
     ground HOL instance in its own nonempty sort (leftover variables name
     opaque nonempty sorts).  TF1 keeps exactly HOL's parametric type
     arguments and binds all formula type variables.  Guards restrict every
     guarded quantifier and gsy result to its HOL carrier; wit witnesses make
     each such carrier inhabited.  Thus each family extends a HOL model and
     cannot prove a non-theorem merely by confusing types. *)
  fun encode_formula symbols encoding needs formula =
    let
      fun encode (FOQuant (all, vars, body)) =
            List.foldr (fn (var, result) =>
              let
                val ty = type_of var
                val var_name = variable_name (fst (dest_var var))
                val bound = (var_name, SOME (type_for encoding ty))
                val result' =
                  if guarded_type encoding needs ty then
                    if all then hhTptpProblem.Conn (hhTptpProblem.Implies,
                      [guard_atom ty
                        (hhTptpProblem.Tm ((var_name, []), [])), result])
                    else hhTptpProblem.Conn (hhTptpProblem.And,
                      [guard_atom ty
                        (hhTptpProblem.Tm ((var_name, []), [])), result])
                  else result
              in
                hhTptpProblem.Quant (all, [bound], result')
              end) (encode body) vars
        | encode (FOConn (conn, bodies)) =
            hhTptpProblem.Conn (conn, map encode bodies)
        (* Equality of non-boolean HOL terms remains an atomic HOL formula
           through the skeleton pass.  Its temporary $equal head represents
           TPTP equality, not a first-class boolean symbol: printing it as a
           term gives ill-typed TFF/TX0 to Vampire. *)
        | encode (FOAtom (FOHead (head, [left, right]))) =
            if raw_symbol head = "$equal" then
              hhTptpProblem.Conn (hhTptpProblem.Equal,
                [hhTptpProblem.Atom (encode_term symbols encoding left),
                 hhTptpProblem.Atom (encode_term symbols encoding right)])
            else hhTptpProblem.Atom
              (encode_term symbols encoding (FOHead (head, [left, right])))
        | encode (FOAtom tm) =
            hhTptpProblem.Atom (encode_term symbols encoding tm)
      val result = encode formula
    in
      case encoding of
          hhTypeEnc.Native {poly = true, ...} =>
            (case type_vars_of_formula formula of
                [] => result
              | tvars => hhTptpProblem.TyQuant (true,
                  map (fn ty => "A" ^ aiLib.escape (dest_vartype ty)) tvars,
                  result))
        | _ => result
    end

  (* These accumulate symbol occurrences in reverse; distinct_heads of
     the reversed result lists each head once, in occurrence order. *)
  fun heads_of_fo_term (FOHead (head, args), heads) =
        List.foldl heads_of_fo_term
          (if is_symbol head then head :: heads else heads) args
    | heads_of_fo_term (FOValue head, heads) =
        if is_symbol head then head :: heads else heads
    | heads_of_fo_term (FOApp {left, right, ...}, heads) =
        heads_of_fo_term (right, heads_of_fo_term (left, heads))
    | heads_of_fo_term (FOPred body, heads) = heads_of_fo_term (body, heads)
    | heads_of_fo_term (FOAbs (_, body), heads) = heads_of_fo_term (body, heads)
  fun heads_of_fo_formula (FOQuant (_, _, body), heads) =
        heads_of_fo_formula (body, heads)
    | heads_of_fo_formula (FOConn (_, bodies), heads) =
        List.foldl heads_of_fo_formula heads bodies
    | heads_of_fo_formula (FOAtom tm, heads) = heads_of_fo_term (tm, heads)

  fun generic_proxy_type head =
    let
      val alpha = Type.alpha
      val predicate = alpha --> Type.bool
    in
      case raw_symbol head of
          "pxy.eq" => alpha --> alpha --> Type.bool
        | "pxy.all" => predicate --> Type.bool
        | "pxy.ex" => predicate --> Type.bool
        | "$ite" => Type.bool --> alpha --> alpha --> alpha
        | _ =>
            if is_const head then
              let val {Thy, Name, ...} = dest_thy_const head in
                type_of (prim_mk_const {Thy = Thy, Name = Name})
              end
            else type_of head
    end

  fun declaration_type encoding arity head =
    let
      val full_type =
        case encoding of
            hhTypeEnc.Native {poly = true, ...} => generic_proxy_type head
          | _ => type_of head
      fun consume 0 ty domains = (List.rev domains, ty)
        | consume count ty domains =
            (case dom_rng ty of
                 SOME (domain, range) =>
                   consume (count - 1) range (domain :: domains)
               | NONE => fail "symbol arity exceeds its HOL function type")
      val (domains, result) =
        case encoding of
            hhTypeEnc.Native {higher = false, poly = false, ...} =>
              consume arity full_type []
          | _ => strip_fun full_type
      val ty =
        List.foldr (fn (domain, range) =>
          hhTptpProblem.TyFun (type_for encoding domain, range))
          (type_for encoding result) domains
    in
      case encoding of
          hhTypeEnc.Native {poly = true, ...} =>
            let val vars = Type.type_vars full_type in
              if null vars then ty else hhTptpProblem.TyPi
                (map (fn var => "A" ^ aiLib.escape (dest_vartype var)) vars, ty)
            end
        | _ => ty
    end

  (* [distinct] must be the first-occurrence distinct type list (see
     distinct_formula_types): the declarations keep first-occurrence order. *)
  fun type_declarations encoding distinct =
    let
      fun native_op ty =
        if is_vartype ty then NONE
        else
          let val {Thy, Tyop, Args} = Type.dest_thy_type ty in
            SOME (aiLib.escape ("ty." ^ Thy ^ "." ^ Tyop), length Args)
          end
      fun operator_compare ((symbol, arity), (symbol', arity')) =
        case String.compare (symbol, symbol') of
            EQUAL => Int.compare (arity, arity')
          | order => order
      fun declarations operators =
        map (fn (symbol, arity) => hhTptpProblem.TypeDecl
          (aiLib.escape ("ty." ^ symbol), symbol, arity)) operators
    in
      case encoding of
          hhTypeEnc.Native {poly = true, ...} =>
            declarations (aiLib.mk_sameorder_set operator_compare
              (List.mapPartial native_op distinct))
        | _ =>
            map (fn symbol => hhTptpProblem.TypeDecl
              (aiLib.escape ("ty." ^ symbol), symbol, 0))
              (aiLib.mk_sameorder_set String.compare
                (map mangle_type distinct))
    end

  fun gsy_line (symbols : symbols) encoding needs head =
    let
      val (domains, result) = strip_fun (type_of head)
    in
      if not (guarded_type encoding needs result) then NONE
      else
        let
          val variables = ListPair.zip
            (map (fn index => "G" ^ Int.toString index)
               (List.tabulate (length domains, fn index => index)),
             map (type_for encoding) domains)
          val application = hhTptpProblem.Tm
            ((#head symbols head, []),
             map (fn (name, _) =>
               hhTptpProblem.Tm ((name, []), [])) variables)
          val body = guard_atom result application
          val formula = if null variables then body else hhTptpProblem.Quant
            (true, map (fn (name, ty) => (name, SOME ty)) variables, body)
        in
          SOME (hhTptpProblem.FormLine
            (aiLib.escape ("gsy." ^ #head symbols head),
             hhTptpProblem.Axiom, formula))
        end
    end

  fun witness_line encoding ty =
    let
      val witness = aiLib.escape ("wit." ^ mangle_type ty)
      val term = hhTptpProblem.Tm ((witness, []), [])
    in
      hhTptpProblem.FormLine (aiLib.escape ("wit." ^ mangle_type ty),
        hhTptpProblem.Axiom, guard_atom ty term)
    end

  fun is_helper_name name = String.isPrefix "help." name
  fun is_lambda_name name = String.isPrefix "lam." name

  (* Number of the next copy of a name, given the copies seen so far. *)
  fun next_copy name copies =
    case Redblackmap.peek (copies, name) of NONE => 1 | SOME n => n + 1

  fun premise_lines symbols format encoding needs facts =
    let
      fun ident name n =
        if is_lambda_name name then aiLib.escape name
        else aiLib.escape (hhTptpProblem.fact_name n name)
      fun line (name, formula, copies) =
        let val n = next_copy name copies in
          (hhTptpProblem.FormLine
             (ident name n, hhTptpProblem.Axiom,
              encode_formula symbols encoding needs formula),
           if is_lambda_name name then copies
           else Redblackmap.insert (copies, name, n))
        end
      fun loop [] _ result = List.rev result
        | loop (item :: rest) copies result =
            let val (output, copies') = line (#1 item, #2 item, copies) in
              loop rest copies' (output :: result)
            end
    in
      loop facts (Redblackmap.mkDict String.compare) []
    end

  fun helper_tm name args = hhTptpProblem.Tm ((aiLib.escape name, []), args)
  fun helper_atom name args = hhTptpProblem.Atom (helper_tm name args)
  fun helper_line name formula = hhTptpProblem.FormLine
    (aiLib.escape ("help." ^ name), hhTptpProblem.Axiom, formula)

  (* Proxy characterizations are HOL terms, not pre-encoded TPTP snippets.
     Consequently they take precisely the same lambda, monomorphization,
     proxy, application, and type-encoding route as selected premises. *)
  fun proxy_helpers heads =
    let
      fun app head args = list_mk_comb (head, args)
      val all = curry list_mk_forall
      fun domains ty = #1 (strip_fun ty)
      fun helpers head =
        let
          val name = raw_symbol head
          val args = domains (type_of head)
          fun var stem ty = mk_var (stem, ty)
          fun binary make =
            case args of
                [ty, _] =>
                  let
                    val x = var "HX" ty
                    val y = var "HY" ty
                    val proxy = app head [x, y]
                  in
                    [make (all [x, y] (mk_imp (proxy, mk_eq (x, y)))),
                     make (all [x, y] (mk_imp (mk_eq (x, y), proxy)))]
                  end
              | _ => []
          fun proposition make =
            case args of
                [_, _] =>
                  let
                    val p = var "HP" Type.bool
                    val q = var "HQ" Type.bool
                    val rhs = case name of
                        "pxy.conj" => mk_conj (p, q)
                      | "pxy.disj" => mk_disj (p, q)
                      | "pxy.imp" => mk_imp (p, q)
                      | _ => mk_eq (p, q)
                  in [make (all [p, q] (mk_eq (app head [p, q], rhs)))] end
              | _ => []
        in
          case name of
              "pxy.eq" => binary (fn tm => ("help.pxy.eq", tm))
            | "pxy.not" =>
                (case args of
                    [_] => let val p = var "HP" Type.bool in
                      [("help.pxy.not", all [p]
                        (mk_eq (app head [p], mk_neg p)))]
                    end
                  | _ => [])
            | "pxy.conj" => proposition (fn tm => ("help.pxy.conj", tm))
            | "pxy.disj" => proposition (fn tm => ("help.pxy.disj", tm))
            | "pxy.imp" => proposition (fn tm => ("help.pxy.imp", tm))
            | "pxy.all" =>
                (case args of
                    [pty] =>
                      (case dom_rng pty of
                          SOME (xty, _) =>
                            let val p = var "HP" pty
                                val x = var "HX" xty
                            in [("help.pxy.all", all [p, x]
                              (mk_imp (app head [p], app p [x])))] end
                        | NONE => [])
                  | _ => [])
            | "pxy.ex" =>
                (case args of
                    [pty] =>
                      (case dom_rng pty of
                          SOME (xty, _) =>
                            let val p = var "HP" pty
                                val x = var "HX" xty
                            in [("help.pxy.ex", all [p, x]
                              (mk_imp (app p [x], app head [p])))] end
                        | NONE => [])
                  | _ => [])
            | "pxy.true" => [("help.pxy.true", mk_eq (head, T))]
            | "pxy.false" => [("help.pxy.false", mk_eq (head, F))]
            | _ => []
        end
    in
      List.concat (map helpers heads)
    end

  (* pp is introduced only after HOL terms have become first-order terms.
     Its two bridge laws therefore are the sole intentionally AST-level
     helpers.  pxy.true/false are added to the declaration table below. *)
  fun pp_helpers used_pp =
    if not used_pp then []
    else
      [helper_line "pp.true" (helper_atom "pp." [helper_tm "pxy.true" []]),
       helper_line "pp.false" (hhTptpProblem.Conn (hhTptpProblem.Not,
         [helper_atom "pp." [helper_tm "pxy.false" []]]))]

  fun fetched thy name = Thm.concl (DB.fetch thy name)

  fun hol_helpers format mode used_app heads =
    let
      fun has name = List.exists (fn head => raw_symbol head = name) heads
      val has_cond = List.exists is_cond_head heads
      fun comb name theorem =
        if (mode = hhLamTrans.Combs orelse
            mode = hhLamTrans.CombsAndLifting) andalso
           has ("c.combin." ^ name) then
          [("help.combin." ^ name, fetched "combin" theorem)]
        else []
      val combinators =
        comb "I" "I_THM" @ comb "K" "K_THM" @ comb "S" "S_THM" @
        comb "C" "C_THM" @ comb "o" "o_THM"
      val lets =
        if has "c.bool.LET" then [("help.bool.LET", fetched "bool" "LET_THM")]
        else []
      val {with_ite, ...} = syntax_of format
      (* COND_CLAUSE1/2 are implementation theorems rather than exported
         boolTheory bindings.  Construct their closed proposition shapes;
         they still traverse lambda, mono, proxy, and encoding passes. *)
      val conds = if not with_ite andalso has_cond then
        let
          val x = mk_var ("HX", Type.alpha)
          val y = mk_var ("HY", Type.alpha)
          val b = mk_var ("HB", Type.bool)
          fun cond test = list_mk_comb (conditional, [test, x, y])
          (* Where bool is $o, b = T is an iff and this is what $o
             already knows.  Where bool is a term sort read through pp,
             the skeleton would turn b = T into the tautology
             pp(b) <=> pp(true).  The law must equate terms instead, or
             no COND test other than T or F could reach if_True/False:
             build it with the $equal head that stands for TPTP
             equality. *)
          val bool_is_o = is_full_ho format orelse is_fool format
          val term_eq = mk_var ("$equal",
            Type.bool --> Type.bool --> Type.bool)
          fun bool_eq (left, right) =
            if bool_is_o then mk_eq (left, right)
            else list_mk_comb (term_eq, [left, right])
        in
          [("help.if_True", list_mk_forall ([x, y], mk_eq (cond T, x))),
           ("help.if_False", list_mk_forall ([x, y], mk_eq (cond F, y))),
           ("help.bool_cases", mk_forall (b,
             mk_disj (bool_eq (b, T), bool_eq (b, F))))]
        end
        else []
    in
      combinators @ lets @ conds
    end

  fun fold_apps_term add (FOHead (_, args), result) =
        List.foldl (fold_apps_term add) result args
    | fold_apps_term _ (FOValue _, result) = result
    | fold_apps_term add (FOApp (app as {left, right, ...}), result) =
        fold_apps_term add
          (right, fold_apps_term add (left, add (app, result)))
    | fold_apps_term add (FOPred body, result) =
        fold_apps_term add (body, result)
    | fold_apps_term add (FOAbs (_, body), result) =
        fold_apps_term add (body, result)

  fun fold_apps_formula add (FOQuant (_, _, body), result) =
        fold_apps_formula add (body, result)
    | fold_apps_formula add (FOConn (_, bodies), result) =
        List.foldl (fold_apps_formula add) result bodies
    | fold_apps_formula add (FOAtom tm, result) =
        fold_apps_term add (tm, result)

  fun add_app_signature ({function_type, argument_type, result_type, ...}
                         : fo_app,
                         signatures) =
    (function_type, argument_type, result_type) :: signatures

  fun app_function_types formulas =
    let
      fun add ({function_type, ...} : fo_app, state as (seen, types)) =
        if Redblackset.member (seen, function_type) then state
        else (Redblackset.add (seen, function_type), function_type :: types)
    in
      rev (#2 (List.foldl (fold_apps_formula add)
        (Redblackset.empty Type.compare, []) formulas))
    end

  fun add_head_arity head arity table =
    case Redblackmap.peek (table, head) of
        SOME old =>
          if arity < old then Redblackmap.insert (table, head, arity)
          else table
      | NONE => Redblackmap.insert (table, head, arity)

  fun head_arities_term (FOHead (head, args), result) =
        List.foldl head_arities_term
          (if is_symbol head then add_head_arity head (length args) result
           else result) args
    | head_arities_term (FOValue _, result) = result
    | head_arities_term (FOApp {left, right, ...}, result) =
        head_arities_term (right, head_arities_term (left, result))
    | head_arities_term (FOPred body, result) =
        head_arities_term (body, result)
    | head_arities_term (FOAbs (_, body), result) =
        head_arities_term (body, result)

  fun head_arities_formula (FOQuant (_, _, body), result) =
        head_arities_formula (body, result)
    | head_arities_formula (FOConn (_, bodies), result) =
        List.foldl head_arities_formula result bodies
    | head_arities_formula (FOAtom tm, result) =
        head_arities_term (tm, result)

  fun value_heads_term (FOHead (_, args), result) =
        List.foldl value_heads_term result args
    | value_heads_term (FOValue head, result) =
        if is_bound_var head then result else head :: result
    | value_heads_term (FOApp {left, right, ...}, result) =
        value_heads_term (right, value_heads_term (left, result))
    | value_heads_term (FOPred body, result) =
        value_heads_term (body, result)
    | value_heads_term (FOAbs (_, body), result) =
        value_heads_term (body, result)

  fun value_heads_formula (FOQuant (_, _, body), result) =
        value_heads_formula (body, result)
    | value_heads_formula (FOConn (_, bodies), result) =
        List.foldl value_heads_formula result bodies
    | value_heads_formula (FOAtom tm, result) =
        value_heads_term (tm, result)

  fun generated_problem format encoding needs
      ({conjecture, facts, used_app, used_pp} : fo_ir) direct_helpers =
    let
      val all_formulas = conjecture :: map #2 facts
      val symbols = symbol_table encoding
      val typed = format <> hhTptpProblem.FOF
      val guarded = case encoding of hhTypeEnc.Guards _ => true | _ => false
      fun declared head =
        let val name = raw_symbol head in
          name = "$ite" orelse not (String.isPrefix "$" name)
        end
      fun unique_symbols [] _ = []
        | unique_symbols (head :: rest) seen =
            let val symbol = #head symbols head in
              if Redblackset.member (seen, symbol) then
                unique_symbols rest seen
              else head ::
                unique_symbols rest (Redblackset.add (seen, symbol))
            end
      val declaration_heads =
        if typed orelse guarded then
          let
            val bool_proxies = if used_pp then
              [mk_var ("pxy.true", Type.bool),
               mk_var ("pxy.false", Type.bool)]
              else []
            val heads = distinct_heads
              (rev (List.foldl heads_of_fo_formula [] all_formulas) @
               bool_proxies)
          in
            unique_symbols (List.filter declared heads)
              (Redblackset.empty String.compare)
          end
        else []
      val all_types =
        if typed orelse guarded then distinct_formula_types all_formulas
        else []
      val decls =
        if not typed then []
        else
          let
            val head_arities = List.foldl head_arities_formula
              (Redblackmap.mkDict Term.compare) all_formulas
            fun head_arity head =
              Option.getOpt (Redblackmap.peek (head_arities, head), 0)
            val sym_decls = map (fn head => hhTptpProblem.SymDecl
              (aiLib.escape ("sy." ^ #head symbols head),
               #head symbols head,
               declaration_type encoding (head_arity head) head))
              declaration_heads
            val app_decls =
              case encoding of
                  hhTypeEnc.Native {poly = false, ...} =>
                    map (fn app_signature as (function_type, argument_type,
                                              result_type) =>
                      let val symbol = #app symbols app_signature in
                        hhTptpProblem.SymDecl
                          (aiLib.escape ("sy." ^ symbol), symbol,
                           hhTptpProblem.TyFun
                             (type_for encoding function_type,
                              hhTptpProblem.TyFun
                                (type_for encoding argument_type,
                                 type_for encoding result_type)))
                      end) (aiLib.mk_sameorder_set signature_compare
                        (rev (List.foldl (fold_apps_formula add_app_signature)
                          [] all_formulas)))
                | _ => if used_app then [hhTptpProblem.SymDecl
                    ("sy_2Eapp", "app_2E", hhTptpProblem.TyFun
                      (hhTptpProblem.TyCon ("$i", []),
                       hhTptpProblem.TyFun
                         (hhTptpProblem.TyCon ("$i", []),
                          hhTptpProblem.TyCon ("$i", []))))]
                  else []
            (* Only mono native values get symbols of their own; elsewhere
               a value is its head, which sym_decls already declares. *)
            val value_decls =
              case encoding of
                  hhTypeEnc.Native {poly = false, ...} =>
                    map (fn head => hhTptpProblem.SymDecl
                      (aiLib.escape ("sy." ^ #value symbols head),
                       #value symbols head,
                       type_for encoding (type_of head)))
                      (distinct_heads
                        (rev (List.foldl value_heads_formula [] all_formulas)))
                | _ => []
            val pp_decls = if used_pp then [hhTptpProblem.SymDecl
              ("sy_2Epp", "pp_2E", hhTptpProblem.TyFun
                (type_for encoding Type.bool,
                 hhTptpProblem.TyCon ("$o", [])))]
              else []
          in
            type_declarations encoding all_types @ sym_decls @ app_decls @
            value_decls @ pp_decls
          end
      val gsy = if guarded then
        List.mapPartial (gsy_line symbols encoding needs) declaration_heads
        else []
      val guard_types =
        List.filter (guarded_type encoding needs) all_types
      val witnesses = map (witness_line encoding) guard_types
      val (helpers, ordinary) = List.partition (is_helper_name o #1) facts
      fun helper_lines facts =
        let
          fun loop [] _ result = List.rev result
            | loop ((name, formula) :: rest) seen result =
                let
                  val n = next_copy name seen
                  val suffix = if n = 1 then "" else "." ^ Int.toString n
                  val line = hhTptpProblem.FormLine
                    (aiLib.escape (name ^ suffix), hhTptpProblem.Axiom,
                     encode_formula symbols encoding needs formula)
                in
                  loop rest (Redblackmap.insert (seen, name, n))
                    (line :: result)
                end
        in
          loop facts (Redblackmap.mkDict String.compare) []
        end
      val conjecture' = hhTptpProblem.FormLine ("conjecture",
        hhTptpProblem.Conjecture,
        encode_formula symbols encoding needs conjecture)
    in
      [("Declarations", decls @ gsy @ witnesses),
       ("Helpers", helper_lines helpers @ direct_helpers),
       ("Facts", premise_lines symbols format encoding needs ordinary),
       ("Conjecture", [conjecture'])]
    end

  (* The formulas the ?? monotonicity oracle reads; none for the other
     encodings, so that the deferred tail keeps no HOL terms alive for
     it. *)
  fun needs_input encoding main_terms helpers =
    case encoding of
        hhTypeEnc.Guards {level = hhTypeEnc.NonmonoNonUniform, ...} =>
          #conjecture main_terms ::
          map #2 (#facts main_terms @ helpers)
      | _ => []

  (* Everything up to the TPTP AST that resolves terms or draws fresh
     names runs here, on the caller, and what is left (the tail) neither
     draws nor consults the memo, theorem data or the translation cache.
     The tail reads the live signature and type database and builds the
     AST; its failures are raw (see describe_failure). *)
  fun make_problem names main_is_mono options lambda_terms =
    let
      val {format, type_enc, lam_trans, mono_iters, mono_instances} = options
      val caps = {max_iters = mono_iters, max_new_instances = mono_instances}
      val main_terms = if main_is_mono then lambda_terms
                       else monomorph_with names type_enc caps lambda_terms
      (* firstorderize reads only the conjecture and facts, so the proxy
         names are not recorded.  The main problem is transformed once;
         helper lists are transformed alone and appended to it. *)
      val proxied = proxy_formula format (fn _ => ())
      fun proxy_facts facts = map (fn (name, tm) =>
        (name, proxied (skeleton tm))) facts
      val main_conjecture = proxied (skeleton (#conjecture main_terms))
      val main_facts = proxy_facts (#facts main_terms)
      fun firstorder helpers = firstorderize format type_enc
        {conjecture = main_conjecture,
         facts = main_facts @ proxy_facts helpers}
      fun heads_of ({conjecture, facts, ...} : fo_ir) =
        distinct_heads (rev (heads_of_fo_formula (conjecture,
          List.foldl (fn ((_, formula), heads) =>
            heads_of_fo_formula (formula, heads)) [] facts)))
      (* Helpers have the original problem as their monomorphization ground
         pool.  They are then firstorderized together with it, so application
         arities and the final symbol table are shared by every section. *)
      val main_pool =
        if is_monomorphic type_enc then
          SOME (hhMonomorph.mk_pool_with names (list_mk_conj
            (#conjecture main_terms :: map #2 (#facts main_terms))))
        else NONE
      fun translate_helpers source =
        if null source then []
        else
          let
            (* [lambda_terms] can contain very large combinator expansions.
               In pure-combs mode the pass creates no lambda definitions, so
               translate only the new helpers and add the already translated
               main problem back as the monomorphization ground pool.  The
               other modes retain their shared naming pass for generated
               lifting definitions. *)
            val (lambda_terms', retention_source) =
              if lam_trans = hhLamTrans.Combs then
                let
                  val helpers = #facts (lambda_with names format lam_trans
                    (presimp format {conjecture = T, facts = source}))
                in
                  ({conjecture = #conjecture main_terms,
                    facts = #facts main_terms @ helpers}, helpers)
                end
              else
                let
                  val translated = lambda_with names format lam_trans
                    (presimp format
                      {conjecture = #conjecture lambda_terms,
                       facts = #facts lambda_terms @ source})
                in
                  (translated, #facts translated)
                end
            val helper_source = List.filter (is_helper_name o #1)
              (#facts lambda_terms')
            val translated =
              case main_pool of
                  SOME pool =>
                    hhMonomorph.monomorph_pool caps pool helper_source
                | NONE => helper_source
            (* A schematic proxy law with no ground instance is still sound:
               the mono printer gives its remaining type variables opaque
               sorts.  Do not silently lose it as an "ignored" user fact. *)
            fun found name = List.exists (fn (other, _) => other = name)
              translated
            val retained = List.filter (fn (name, _) =>
              is_helper_name name andalso not (found name)) retention_source
          in
            translated @ retained
          end
      (* The caller-side first-orderizations report as the tail's
         failures do after describe_failure. *)
      fun firstorder_now helpers = firstorder helpers
        handle (exn as Lambda_survived _) => raise describe_failure exn
      val main_fo = firstorder_now []
      val main_heads = heads_of main_fo
      val initial = hol_helpers format lam_trans (#used_app main_fo) main_heads
      val preliminary_helpers = translate_helpers initial
      val (preliminary_fo, preliminary_heads) =
        if null preliminary_helpers then (main_fo, main_heads)
        else
          let val fo = firstorder_now preliminary_helpers in
            (fo, heads_of fo)
          end
      val proxy_source = proxy_helpers preliminary_heads
      val with_proxies = initial @ proxy_source
      (* EQ_EXT's only constant is equality, and app is introduced only
         after monomorphization, so the ground pool seldom grounds it at a
         function type that app is used at.  A mono problem then got
         EQ_EXT only at opaque sorts, where it is useless: two lifted
         lambdas, say, could never be proved equal.  Show the
         monomorphizer an equation at each app function type.  EQ_EXT has
         no lambda in term position, so the lambda pass would not change
         it. *)
      val extensionality =
        if not (#used_app main_fo) then []
        else
          let
            val ext = ("help.eq_ext", Thm.concl boolTheory.EQ_EXT)
          in
            case main_pool of
                NONE => [ext]
              | SOME main_pool =>
                let
                  val {conjecture, facts, ...} = preliminary_fo
                  val app_types = app_function_types
                    (conjecture :: map #2 facts)
                  fun witness ty = let val f = mk_var ("f", ty) in
                    mk_eq (f, f)
                  end
                  val pool = hhMonomorph.extend_pool main_pool
                    (map witness app_types)
                in
                  case hhMonomorph.monomorph_pool caps pool [ext] of
                      [] => [ext]
                    | instances => instances
                end
          end
      val helper_terms = translate_helpers with_proxies @ extensionality
      val needs_terms = needs_input type_enc main_terms helper_terms
      val final_firstorder =
        if null helper_terms then fn () => main_fo
        else fn () => firstorder helper_terms
    in
      fn () =>
        let
          val final_fo = final_firstorder ()
          val needs = hhTypeEnc.types_needing_encoding needs_terms
        in
          generated_problem format type_enc needs final_fo
            (pp_helpers (#used_pp final_fo))
        end
    end

  type tail = unit -> hhTptpProblem.problem

  fun force_tail tail = tail () handle exn => raise describe_failure exn

  fun generate_problem options terms =
    let
      val {format, type_enc, lam_trans, mono_iters, mono_instances} = options
      val simplified = presimp format terms
      val pre_mono =
        lam_trans = hhLamTrans.Combs andalso is_monomorphic type_enc
      val lambda_input = if pre_mono then
        pass_monomorph type_enc
          {max_iters = mono_iters, max_new_instances = mono_instances}
          simplified
        else simplified
    in
      force_tail (make_problem hhNames.global pre_mono options
        (pass_lambda format lam_trans lambda_input))
    end

  type export_memo =
    {entries : (hhLamTrans.mode * named_terms * named_terms) list ref,
     runs : int ref, names : hhNames.supply}

  fun new_export_memo_with names = {entries = ref [], runs = ref 0,
                                    names = names}
  fun new_export_memo () = new_export_memo_with hhNames.global
  fun memo_lambda_runs ({runs, ...} : export_memo) = !runs

  fun same_terms left right =
    Term.aconv (#conjecture left) (#conjecture right) andalso
    ListPair.allEq (fn ((left_name, left_tm), (right_name, right_tm)) =>
      left_name = right_name andalso Term.aconv left_tm right_tm)
      (#facts left, #facts right)

  fun memoized_lambda ({entries, runs, names} : export_memo) format mode
      terms =
    let val key = effective_mode format mode in
      case List.find (fn (old_key, old_terms, _) => old_key = key andalso
          same_terms old_terms terms) (!entries) of
          SOME (_, _, result) => result
        | NONE =>
            let val result = lambda_with names format mode terms in
              entries := (key, terms, result) :: !entries;
              runs := !runs + 1;
              result
            end
    end

  fun encoding_name (hhTypeEnc.Native {higher, fool, poly}) =
        (if poly then "poly_native" else "mono_native") ^
        (if higher then "_higher" else "") ^ (if fool then "_fool" else "")
    | encoding_name (hhTypeEnc.Guards {poly, level}) =
        (if poly then "poly_guards" else "mono_guards") ^
        (case level of
             hhTypeEnc.AllTypes => ""
           | hhTypeEnc.NonmonoNonUniform => "??")
    | encoding_name hhTypeEnc.LegacySP = "legacy"

  fun header ({format, type_enc, lam_trans, mono_iters, mono_instances}
              : problem_options) =
    "generated by hhProblemGen; format=" ^
    hhTptpProblem.format_name format ^
    "; type_enc=" ^ encoding_name type_enc ^ "; lam_trans=" ^
    hhLamTrans.mode_name lam_trans ^
    "; mono_iters=" ^ Int.toString mono_iters ^
    "; mono_instances=" ^ Int.toString mono_instances

  fun write_problem file text =
    let val output = TextIO.openOut file in
      (TextIO.output (output, text); TextIO.closeOut output)
      handle error => (TextIO.closeOut output handle _ => (); raise error)
    end

  (* The caller-side stage: everything that draws fresh names or reads the
     memo, theorem data or the translation cache.  The tail it returns
     builds the TPTP AST and may run on another thread. *)
  fun prepare_pb memo options (conjecture, named) =
    let
      val input = presimp (#format options) {conjecture = conjecture,
        facts = map (fn (name, theorem) =>
          (name, Thm.concl theorem)) named}
      val {type_enc, lam_trans, mono_iters, mono_instances, ...} = options
      val pre_mono =
        lam_trans = hhLamTrans.Combs andalso is_monomorphic type_enc
      val names = #names memo
      val lambda_input = if pre_mono then
        monomorph_with names type_enc
          {max_iters = mono_iters, max_new_instances = mono_instances} input
        else input
      val lambda_terms = if pre_mono then
        lambda_with names (#format options) lam_trans lambda_input
        else memoized_lambda memo (#format options) lam_trans lambda_input
    in
      make_problem names pre_mono options lambda_terms
    end

  (* The AST-only stage: no HOL terms, no fresh names. *)
  fun format_pb options problem =
    hhTptpProblem.string_of_problem (#format options) (header options)
      problem

  fun export_pb_in memo options file input =
    write_problem file
      (format_pb options (force_tail (prepare_pb memo options input)))

  fun export_pb options file input =
    export_pb_in (new_export_memo ()) options file input

end
