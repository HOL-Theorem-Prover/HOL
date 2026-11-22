structure hhTypeEnc :> hhTypeEnc =
struct

  open HolKernel boolSyntax

  type hol_type = Type.hol_type
  type term = Term.term

  datatype type_level = AllTypes | NonmonoNonUniform
  datatype type_enc =
      Native of {higher : bool, fool : bool, poly : bool}
    | Guards of {poly : bool, level : type_level}
    | LegacySP

  fun fail message = raise Fail ("hhTypeEnc: " ^ message)

  fun format_of_string "fof" = hhTptpProblem.FOF
    | format_of_string "tf0" =
        hhTptpProblem.TFF {poly = false, fool = hhTptpProblem.NoFool}
    | format_of_string "tf1" =
        hhTptpProblem.TFF {poly = true, fool = hhTptpProblem.NoFool}
    | format_of_string "tx0" = hhTptpProblem.TFF
        {poly = false, fool = hhTptpProblem.Fool {with_ite = true,
                                                  with_let = true}}
    | format_of_string "tx0-" = hhTptpProblem.TFF
        {poly = false, fool = hhTptpProblem.Fool {with_ite = false,
                                                  with_let = false}}
    | format_of_string "th0" = hhTptpProblem.THF
        {poly = false, syntax = {with_ite = false, with_let = false},
         choice = false}
    | format_of_string "th1" = hhTptpProblem.THF
        {poly = true, syntax = {with_ite = true, with_let = false},
         choice = false}
    | format_of_string format =
        fail ("unknown format " ^ String.toString format)

  fun valid_format format =
    (ignore (format_of_string format); true) handle Fail _ => false

  (* The slice vocabulary: names and encodings must stay mutually inverse,
     so keep them in one table rather than two mirrored case analyses. *)
  val encodings =
    [("mono_native", Native {higher = false, fool = false, poly = false}),
     ("mono_native_fool", Native {higher = false, fool = true, poly = false}),
     ("mono_native_higher",
      Native {higher = true, fool = false, poly = false}),
     ("mono_native_higher_fool",
      Native {higher = true, fool = true, poly = false}),
     ("poly_native", Native {higher = false, fool = false, poly = true}),
     ("mono_guards", Guards {poly = false, level = AllTypes}),
     ("mono_guards??", Guards {poly = false, level = NonmonoNonUniform}),
     ("", LegacySP)]

  fun of_string string =
    case List.find (fn (name, _) => name = string) encodings of
        SOME (_, enc) => enc
      | NONE => fail ("unknown type encoding " ^ String.toString string)

  fun to_string enc =
    case List.find (fn (_, other) => other = enc) encodings of
        SOME (name, _) => name
      | NONE => fail "encoding is outside the slice vocabulary"

  fun has_fool hhTptpProblem.NoFool = false
    | has_fool (hhTptpProblem.Fool _) = true

  fun syntax_has_fool {with_ite, with_let} = with_ite orelse with_let

  fun adjust_type_enc hhTptpProblem.FOF (Native _) =
        Guards {poly = false, level = AllTypes}
    | adjust_type_enc hhTptpProblem.FOF (enc as Guards {poly = false, ...}) =
        enc
    | adjust_type_enc hhTptpProblem.FOF (Guards {poly = true, ...}) =
        fail "polymorphic guards are not in the slice vocabulary"
    | adjust_type_enc hhTptpProblem.FOF LegacySP = LegacySP
    | adjust_type_enc (hhTptpProblem.TFF {poly, fool})
        (Native {fool = wants_fool, poly = wants_poly, ...}) =
        Native {higher = false, fool = wants_fool andalso has_fool fool,
                poly = wants_poly andalso poly}
    | adjust_type_enc (hhTptpProblem.THF {poly, syntax, ...})
        (Native {higher, fool, poly = wants_poly}) =
        Native {higher = higher,
                fool = fool andalso syntax_has_fool syntax,
                poly = wants_poly andalso poly}
    | adjust_type_enc _ LegacySP =
        fail "the legacy s()/p() encoding is valid only with format fof"
    | adjust_type_enc _ (Guards _) =
        fail "guard encodings are valid only with format fof"

  fun type_name ty =
    #Tyop (Type.dest_thy_type ty) handle HOL_ERR _ => ""

  fun is_named names ty = List.exists (fn name => type_name ty = name) names

  fun is_bool ty = type_name ty = "bool"

  fun fun_parts ty = SOME (Type.dom_rng ty) handle HOL_ERR _ => NONE

  fun constructor_arg_types constructor =
    let
      fun split ty =
        case fun_parts ty of
            SOME (left, right) => left :: split right
          | NONE => []
    in
      split (type_of constructor)
    end

  (* A type constructor repeats on a path through one of its constructors
     exactly when the datatype is recursive (including mutual recursion). *)
  fun surely_infinite ty =
    let
      fun at_least_two seen current =
        is_bool current orelse infinite seen current orelse
        (case fun_parts current of
             SOME (_, range) => at_least_two seen range
           | NONE =>
               case TypeBase.fetch current of
                   NONE => false
                 | SOME info =>
                     let val constructors = TypeBasePure.constructors_of info in
                       length constructors >= 2 orelse
                       List.exists (fn constructor =>
                         List.exists (at_least_two seen)
                           (constructor_arg_types constructor)) constructors
                     end)
      and infinite seen current =
        if is_named ["num", "int", "rat", "real", "string"] current then
          true
        else
          case fun_parts current of
              SOME (domain, range) =>
                infinite seen range orelse
                (infinite seen domain andalso at_least_two seen range)
            | NONE => datatype_infinite seen current
      and datatype_infinite seen current =
        let
          val name = type_name current
        in
          if List.exists (fn old => old = name) seen then
            true
          else
            case TypeBase.fetch current of
                NONE => false
              | SOME info =>
                  List.exists (fn constructor =>
                    List.exists (infinite (name :: seen))
                      (constructor_arg_types constructor))
                    (TypeBasePure.constructors_of info)
        end
    in
      infinite [] ty
    end

  fun is_fequal_head head =
    let
      val name =
        if is_const head then fst (dest_const head)
        else if is_var head then fst (dest_var head)
        else ""
    in
      name = "fequal" orelse name = "pxy.eq"
    end

  fun types_needing_encoding formulas =
    let
      fun insert_type ty (state as (seen, types)) =
        if Redblackset.member (seen, ty) then state
        else (Redblackset.add (seen, ty), ty :: types)

      fun is_universal tm vars =
        is_var tm andalso List.exists (fn var => aconv tm var) vars

      fun scan_term vars tm types =
        let
          val (head, args) = strip_comb tm
          val types =
            if is_fequal_head head then
              List.foldl (fn (arg, result) =>
                if is_universal arg vars then insert_type (type_of arg) result
                else result) types args
            else types
        in
          List.foldl (fn (arg, result) => scan_term vars arg result) types args
        end

      fun scan_formula vars positive tm types =
        if is_forall tm then
          let val (var, body) = dest_forall tm in
            scan_formula (var :: vars) positive body types
          end
        else if is_exists tm then
          let val (_, body) = dest_exists tm in
            scan_formula vars positive body types
          end
        else if is_neg tm then
          scan_formula vars (not positive) (dest_neg tm) types
        else if is_imp_only tm then
          let val (left, right) = dest_imp tm in
            scan_formula vars (not positive) left
              (scan_formula vars positive right types)
          end
        else if is_conj tm orelse is_disj tm then
          scan_formula vars positive (lhand tm)
            (scan_formula vars positive (rand tm) types)
        else if is_eq tm then
          let
            val (left, right) = dest_eq tm
            val types =
              if positive andalso is_universal left vars then
                insert_type (type_of left) types
              else types
            val types =
              if positive andalso is_universal right vars then
                insert_type (type_of right) types
              else types
          in
            scan_term vars left (scan_term vars right types)
          end
        else scan_term vars tm types

      fun scan_one tm types =
        scan_formula (free_vars_lr tm) true tm types

      val (_, maybe_nonmono) =
        List.foldl (fn (formula, types) => scan_one formula types)
          (insert_type Type.bool (Redblackset.empty Type.compare, []))
          formulas
    in
      List.filter (not o surely_infinite) (rev maybe_nonmono)
    end

end
