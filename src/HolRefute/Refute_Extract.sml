structure Refute_Extract = struct
  type term = Term.term
  type hol_type = Type.hol_type
  structure Util = Refute_Util

  exception NotExtractable of string list

  (* Strict is the existing native-QC representation.  In Lazy, every HOL
     value is represented by a suspension.  For an algebraic type the
     suspension exposes one raw constructor whose fields are themselves
     suspended; a function suspension exposes a function between suspended
     values.  Consequently constructors allocate without forcing fields,
     and only eliminators (case, primitive observation, and equality) force.
     Keep the two modes explicit: adding thunks to strict QC would change its
     cost and, more importantly, its candidate evaluation behavior. *)
  datatype extraction_mode = Strict | Lazy

  type extraction =
    { source : string,
      entry : string }

  type registered_extraction =
    { source : string,
      entry : string,
      table : int }

  datatype ml_ty =
      MLVar of string
    | MLBool
    | MLIntInf
    | MLChar
    | MLString
    | MLUnit
    | MLTuple of ml_ty list
    | MLOption of ml_ty
    | MLList of ml_ty
    | MLArrow of ml_ty * ml_ty
    | MLWord of int
    | MLDatatype of string
    | MLSusp of ml_ty

  type type_compilation =
    { source : string,
      ml_type : string }

  val reserved =
    ["abstype", "and", "andalso", "as", "case", "datatype", "do",
     "else", "end", "eqtype", "exception", "fn", "fun", "functor",
     "handle", "if", "in", "include", "infix", "infixr", "let",
     "local", "nonfix", "of", "op", "open", "orelse", "raise",
     "rec", "sharing", "sig", "signature", "struct", "structure",
     "then", "type", "val", "where", "while", "withtype"]

  fun fix_reserved name =
    if Lib.mem name reserved then name ^ "_" else name

  (* SML names generated for binders must not identify distinct HOL names.
     Prefix every name and escape every non-alphanumeric character, including
     underscore and apostrophe, so the result is also always an SML value id. *)
  fun clean_name name =
    let
      fun clean character =
        if Char.isAlpha character orelse Char.isDigit character then
          String.str character
        else if character = #"_" then "_u"
        else if character = #"'" then "_p"
        else "_x" ^ Int.fmt StringCvt.HEX (Char.ord character) ^ "_"
    in
      fix_reserved ("v_" ^ String.concat (map clean (String.explode name)))
    end

  (* Generated datatype constructors, generated functions and SML type
     variables carry no HOL binding, so they need legal characters rather
     than injectivity: a fresh serial already separates the names Refute
     mints, and escaping them only makes the emitted source unreadable. *)
  fun sanitize_name name =
    let
      fun clean character =
        if Char.isAlphaNum character orelse character = #"_" orelse
           character = #"'" then character
        else #"_"
      val cleaned = String.map clean name
    in
      if cleaned = "" then "x"
      else if Char.isDigit (String.sub (cleaned, 0)) then "x_" ^ cleaned
      else fix_reserved cleaned
    end

  fun upper_name name = "C_" ^ sanitize_name name
  fun lower_name name = "f_" ^ sanitize_name name

  fun same_term left right = Term.compare (left, right) = EQUAL

  fun kname tm =
    let val {Thy, Name, ...} = Term.dest_thy_const tm
    in (Thy, Name) end

  fun kname_text (thy, name) = thy ^ "$" ^ name

  fun quote text = Portable.mlquote text

  val join = String.concatWith
  val integer = Int.toString

  fun parens text = "(" ^ text ^ ")"

  (* A compiled value is generally not an atom: [constructor_expression]
     returns [SOME (x)] and [C_Foo (x)], a partially applied primitive
     returns an abstraction, [Susp.force (x)] is an application, and so
     are most [strict_primitive] results.  Nearly every position accepts
     that — infix operands, tuple and list components, case scrutinees and
     application heads all parse as intended — but an application
     *argument* does not: splicing [SOME (x)] after a function name
     silently supplies two arguments where one was meant, and the emitted
     program then fails to compile as a whole.  [atom] is the safe splice
     for those positions.  It is the identity on text that is already an
     atom, which is the common case (argument positions are usually filled
     by a variable name), so trace dumps of the generated source do not
     fill up with redundant brackets. *)
  fun is_atom text =
    let
      val count = String.size text
      (* [literal] resumes after a string body, so that a bracket inside
         "..." can never balance a bracket outside it. *)
      fun literal index =
        if index >= count then NONE
        else
          case String.sub (text, index) of
              #"\\" => literal (index + 2)
            | #"\"" => SOME (index + 1)
            | _ => literal (index + 1)
      fun simple index =
        index >= count orelse
        let val character = String.sub (text, index)
        in
          (Char.isAlphaNum character orelse character = #"_" orelse
           character = #"'" orelse character = #".") andalso
          simple (index + 1)
        end
      fun scan opening closing index depth =
        if index >= count then false
        else
          let val character = String.sub (text, index)
          in
            if character = #"\"" then
              (case literal (index + 1) of
                   NONE => false
                 | SOME next => scan opening closing next depth)
            else if character = #"#" andalso index + 1 < count andalso
                    String.sub (text, index + 1) = #"\"" then
              (case literal (index + 2) of
                   NONE => false
                 | SOME next => scan opening closing next depth)
            else if character = opening then
              scan opening closing (index + 1) (depth + 1)
            else if character = closing then
              (if depth = 1 then index = count - 1
               else scan opening closing (index + 1) (depth - 1))
            else scan opening closing (index + 1) depth
          end
      fun encloses opening closing =
        count >= 2 andalso String.sub (text, 0) = opening andalso
        scan opening closing 0 0
    in
      count > 0 andalso
      (simple 0 orelse encloses #"(" #")" orelse encloses #"[" #"]" orelse
       (String.sub (text, 0) = #"\"" andalso literal 1 = SOME count))
    end

  fun atom text = if is_atom text then text else parens text

  fun intinf_literal text =
    "(valOf (IntInf.fromString " ^ quote text ^ ") : IntInf.int)"

  fun num_literal number = intinf_literal (Arbnum.toString number)
  fun int_literal integer =
    let val text = Arbint.toString integer
    in intinf_literal (String.substring (text, 0, String.size text - 1)) end

  fun lazy_delay body = "Susp.delay (fn () => " ^ body ^ ")"
  fun lazy_force value = "Susp.force " ^ parens value
  fun lazy_defer value = lazy_delay (lazy_force value)

  fun strict_apply function argument =
    parens (function ^ " " ^ parens argument)

  fun lazy_apply function argument =
    lazy_defer (parens (lazy_force function ^ " " ^ parens argument))

  type mode_operations =
    { force : string -> string,
      delay : string -> string,
      defer : string -> string,
      apply : string -> string -> string,
      wrap_type : ml_ty -> ml_ty }

  fun operations Strict : mode_operations =
        {force = Lib.I, delay = Lib.I, defer = Lib.I,
         apply = strict_apply, wrap_type = Lib.I}
    | operations Lazy =
        {force = lazy_force, delay = lazy_delay, defer = lazy_defer,
         apply = lazy_apply, wrap_type = MLSusp}

  fun choose Strict strict _ = strict ()
    | choose Lazy _ lazy = lazy ()

  fun type_name ty =
    Hol_pp.type_to_string ty
    handle Interrupt => raise Interrupt | _ => "<unknown type>"

  fun reject message = raise NotExtractable [message]

  type datatype_desc =
    { hol_ty : hol_type,
      ml_name : string,
      constructors : (term * hol_type list * string) list }

  type context =
    { mode : extraction_mode,
      operations : mode_operations,
      datatypes : datatype_desc list ref,
      types : (hol_type * ml_ty * string) list ref,
      equalities : hol_type list ref,
      definitions : (term * string * int * Thm.thm) list ref,
      definition_groups : term list list ref,
      definition_clauses : (term * string) list ref,
      pending : term list ref,
      compset_items :
        ((string * string) * computeLib.transform list) list option ref,
      next_type : int ref,
      next_const : int ref,
      next_pattern : int ref }

  fun new_context mode : context =
    { mode = mode,
      operations = operations mode,
      datatypes = ref [],
      types = ref [],
      equalities = ref [],
      definitions = ref [],
      definition_groups = ref [],
      definition_clauses = ref [],
      pending = ref [],
      compset_items = ref NONE,
      next_type = ref 0,
      next_const = ref 0,
      next_pattern = ref 0 }

  fun context_operations ({operations, ...} : context) = operations
  fun context_mode ({mode, ...} : context) = mode

  fun lookup_type ({types, ...} : context) ty =
    case List.find (fn (other, _, _) => Util.same_type other ty) (!types) of
      SOME (_, mlty, equality) => SOME (mlty, equality)
    | NONE => NONE

  fun lookup_datatype ({datatypes, ...} : context) ty =
    List.find (fn info => Util.same_type (#hol_ty info) ty) (!datatypes)

  fun fresh_type ({next_type, ...} : context) =
    let val number = !next_type
        val _ = next_type := number + 1
    in "refute_ty_" ^ Int.toString number end

  fun fresh_const ({next_const, ...} : context) base =
    let val number = !next_const
        val _ = next_const := number + 1
    in lower_name base ^ "_" ^ Int.toString number end

  fun fresh_pattern ({next_pattern, ...} : context) prefix =
    let val number = !next_pattern
        val _ = next_pattern := number + 1
    in prefix ^ Int.toString number end

  fun word_width ty =
    let
      val index = wordsSyntax.dest_word_type ty
    in
      Arbnum.toInt (fcpLib.index_to_num index)
    end
    handle Feedback.HOL_ERR _ =>
      reject ("word type has no concrete dimindex: " ^ type_name ty)
         | Overflow =>
      reject ("word width is too large: " ^ type_name ty)

  val is_char_list = Refute_EvalSML.is_char_list_type

  fun classify_primitive context ty =
    let
      val ops = context_operations context
      val wrap_type = #wrap_type ops
      fun algebraic strict =
        choose (context_mode context)
          (fn () => SOME strict) (fn () => NONE)
    in
      if Type.is_vartype ty then
        (* [MLVar] prints as an SML type variable, so its leading quote must
           survive; the binder escaping would turn ['a] into a value id. *)
        SOME (wrap_type (MLVar (sanitize_name (Type.dest_vartype ty))))
      else if Util.same_type ty Type.bool then SOME (wrap_type MLBool)
      else if Util.same_type ty numSyntax.num then SOME (wrap_type MLIntInf)
      else if Util.same_type ty intSyntax.int_ty then SOME (wrap_type MLIntInf)
      else if Util.same_type ty stringSyntax.char_ty then
        SOME (wrap_type MLChar)
      else if is_char_list ty then algebraic MLString
      else if Util.same_type ty oneSyntax.one_ty then SOME (wrap_type MLUnit)
      else if wordsSyntax.is_word_type ty then
        SOME (wrap_type (MLWord (word_width ty)))
      else
        case Lib.total Type.dom_rng ty of
          SOME (domain, range) =>
            SOME (wrap_type (MLArrow (ensure_type context domain,
                                      ensure_type context range)))
        | NONE =>
            (case Lib.total pairSyntax.dest_prod ty of
               SOME (left, right) =>
                 algebraic (MLTuple
                   [ensure_type context left, ensure_type context right])
             | NONE =>
                 (case Lib.total listSyntax.dest_list_type ty of
                    SOME element =>
                      algebraic (MLList (ensure_type context element))
                  | NONE =>
                      (case Lib.total optionSyntax.dest_option ty of
                         SOME element =>
                           algebraic (MLOption (ensure_type context element))
                       | NONE => NONE)))
    end

  and ensure_type context ty =
    case lookup_type context ty of
      SOME (mlty, _) => mlty
    | NONE =>
        let
          val number = !(#next_type context)
          val _ = #next_type context := number + 1
          val equality = "eq_refute_" ^ Int.toString number
          val primitive = classify_primitive context ty
        in
          case primitive of
            SOME mlty =>
              (#types context := (ty, mlty, equality) :: !(#types context);
               mlty)
          | NONE =>
              let
                val info =
                  case TypeBase.fetch ty of
                    SOME found => found
                  | NONE =>
                      reject ("no TypeBase information for " ^ type_name ty)
                val generic_ty = TypeBasePure.ty_of info
                val theta = Type.match_type generic_ty ty
                  handle Feedback.HOL_ERR _ =>
                    reject ("cannot instantiate TypeBase information for " ^
                            type_name ty)
                val constructors = List.map (TypeBasePure.cinst ty)
                  (TypeBasePure.constructors_of info)
                val _ =
                  if null constructors then
                    reject ("abstract or generated type is not extractable: " ^
                            type_name ty)
                  else ()
                val ml_name = fresh_type context
                val mlty =
                  #wrap_type (context_operations context)
                    (MLDatatype ml_name)
                val _ = #types context :=
                  (ty, mlty, equality) :: !(#types context)
                fun constructor_info constructor =
                  let
                    val (arguments, result) =
                      boolSyntax.strip_fun (Term.type_of constructor)
                    val _ =
                      if Util.same_type result ty then ()
                      else reject ("ill-instantiated constructor " ^
                                   kname_text (kname constructor))
                    val (_, name) = kname constructor
                    val cname = upper_name (name ^ "_" ^ ml_name)
                    val _ = List.app (fn arg =>
                      ignore (ensure_type context arg)) arguments
                  in
                    (constructor, arguments, cname)
                  end
                val description =
                  {hol_ty = ty, ml_name = ml_name,
                   constructors = List.map constructor_info constructors}
                val _ = #datatypes context :=
                  description :: !(#datatypes context)
              in
                mlty
              end
        end

  fun ml_ty_text mlty =
    case mlty of
      MLVar name => name
    | MLBool => "bool"
    | MLIntInf => "IntInf.int"
    | MLChar => "Char.char"
    | MLString => "String.string"
    | MLUnit => "unit"
    | MLTuple types => parens (join " * " (List.map ml_ty_text types))
    | MLOption ty => parens (ml_ty_text ty) ^ " option"
    | MLList ty => parens (ml_ty_text ty) ^ " list"
    | MLArrow (domain, range) =>
        parens (ml_ty_text domain ^ " -> " ^ ml_ty_text range)
    | MLWord _ => "IntInf.int"
    | MLDatatype name => name
    | MLSusp ty => parens (ml_ty_text ty) ^ " Susp.susp"

  fun equality_name (context as {equalities, ...} : context) ty =
    (ignore (ensure_type context ty);
     if Util.member_type ty (!equalities) then ()
     else equalities := ty :: !equalities;
     case lookup_type context ty of
       SOME (_, name) => name
     | NONE => raise Fail "Refute_Extract: missing equality name")

  fun datatype_dependencies context ({hol_ty, constructors, ...} :
      datatype_desc) =
    let
      fun collect ty =
        case lookup_datatype context ty of
          SOME info =>
            if Util.same_type hol_ty (#hol_ty info) then [] else [#hol_ty info]
        | NONE =>
            if Type.is_vartype ty then []
            else
              List.concat (List.map collect (#2 (Type.dest_type ty)))
    in
      Lib.mk_set (List.concat
        (List.map (fn (_, arguments, _) =>
          List.concat (List.map collect arguments)) constructors))
    end

  fun reachable context source target =
    let
      fun visit seen ty =
        if Util.member_type ty seen then false
        else if Util.same_type ty target then true
        else
          case lookup_datatype context ty of
            NONE => false
          | SOME info =>
              List.exists (visit (ty :: seen))
                (datatype_dependencies context info)
    in
      visit [] source
    end

  fun datatype_groups context =
    let
      val datatypes = rev (!(#datatypes context))
      fun equivalent left right =
        reachable context (#hol_ty left) (#hol_ty right) andalso
        reachable context (#hol_ty right) (#hol_ty left)
      fun groups [] = []
        | groups (info :: rest) =
            let val (same, other) = List.partition (equivalent info) rest
            in (info :: same) :: groups other end
      val raw = groups datatypes
      fun group_has group ty =
        List.exists (fn info => Util.same_type (#hol_ty info) ty) group
      fun dependencies group = Lib.mk_set
        (List.concat (List.map (datatype_dependencies context) group))
      fun ready emitted group =
        List.all (fn dependency =>
          group_has group dependency orelse
          List.exists (fn done => group_has done dependency) emitted)
          (dependencies group)
      fun order emitted [] = rev emitted
        | order emitted remaining =
            (case List.partition (ready emitted) remaining of
               ([], _) => rev emitted @ remaining
             | (now, later) => order (rev now @ emitted) later)
    in
      order [] raw
    end

  fun constructor_declaration context (_, arguments, name) =
    case arguments of
      [] => name
    | [argument] => name ^ " of " ^ ml_ty_text (ensure_type context argument)
    | _ => name ^ " of " ^
        ml_ty_text (MLTuple (List.map (ensure_type context) arguments))

  fun datatype_declaration context group =
    let
      fun one keyword ({ml_name, constructors, ...} : datatype_desc) =
        keyword ^ " " ^ ml_name ^ " =\n    " ^
        join "\n  | " (List.map (constructor_declaration context)
          constructors)
      val first = one "datatype" (hd group)
      val rest = List.map (one "and") (tl group)
    in
      join "\n" (first :: rest) ^ "\n"
    end

  fun constructor_for context constructor =
    let
      val result = #2 (boolSyntax.strip_fun (Term.type_of constructor))
      val _ = ignore (ensure_type context result)
    in
      case lookup_datatype context result of
        NONE => NONE
      | SOME {constructors, ...} =>
          (case List.find (fn (other, _, _) =>
                    Term.same_const other constructor) constructors of
             SOME item => SOME item
           | NONE => NONE)
    end

  fun enum_expression context ty =
    let
      val ops = context_operations context
      fun nonenumerable () =
        reject ("function equality has non-enumerable domain " ^ type_name ty)
      val delayed = #delay ops
      fun constructor_values (_, arguments, name) =
        let
          fun build [] variables =
                let val raw = case variables of
                      [] => name
                    | [variable] => name ^ " " ^ variable
                    | _ => name ^ " (" ^ join ", " variables ^ ")"
                in "[" ^ delayed raw ^ "]" end
            | build (argument :: rest) variables =
                let val variable = "enum_" ^ Int.toString (length variables)
                in
                  "List.concat (List.map (fn " ^ variable ^ " => " ^
                  build rest (variables @ [variable]) ^ ") " ^
                  atom (enum_expression context argument) ^ ")"
                end
        in
          build arguments []
        end
      fun algebraic () =
        case lookup_datatype context ty of
          SOME {constructors, ...} =>
            (case Refute_Gen.cardinality ty of
               NONE => nonenumerable ()
             | SOME _ =>
                 "List.concat [" ^ join ", "
                   (List.map constructor_values constructors) ^ "]")
        | NONE => nonenumerable ()
    in
      if Util.same_type ty Type.bool then
        "[" ^ delayed "false" ^ ", " ^ delayed "true" ^ "]"
      else if Util.same_type ty oneSyntax.one_ty then
        "[" ^ delayed "()" ^ "]"
      else if Util.same_type ty stringSyntax.char_ty then
        "List.tabulate (256, fn n => " ^ delayed "(Char.chr n)" ^ ")"
      else if wordsSyntax.is_word_type ty andalso word_width ty <= 8 then
        let val count = IntInf.toInt (IntInf.pow (2, word_width ty))
        in
          "List.tabulate (" ^ Int.toString count ^
          ", fn n => " ^ delayed "(IntInf.fromInt n)" ^ ")"
        end
      else
        choose (context_mode context)
          (fn () =>
            case Lib.total optionSyntax.dest_option ty of
                SOME element =>
                  "NONE :: List.map SOME " ^
                  parens (enum_expression context element)
              | NONE =>
                  (case Lib.total pairSyntax.dest_prod ty of
                       SOME (left, right) =>
                         "List.concat (List.map (fn a => List.map " ^
                         "(fn b => (a, b)) " ^
                         parens (enum_expression context right) ^
                         ") " ^ parens (enum_expression context left) ^ ")"
                     | NONE => algebraic ()))
          algebraic
    end

  fun equality_body context ty left right =
    let
      val ops = context_operations context
      val represented = ensure_type context ty
      val mlty = case represented of MLSusp raw => raw | raw => raw
      val force = #force ops
      val left_value = force left
      val right_value = force right
    in
      case mlty of
        MLBool =>
          parens ("(" ^ left_value ^ " andalso " ^ right_value ^
                  ") orelse (not " ^ parens left_value ^
                  " andalso not " ^ parens right_value ^ ")")
      | MLIntInf =>
          "IntInf.compare (" ^ left_value ^ ", " ^ right_value ^
          ") = EQUAL"
      | MLChar =>
          "Char.compare (" ^ left_value ^ ", " ^ right_value ^ ") = EQUAL"
      | MLString =>
          "String.compare (" ^ left_value ^ ", " ^ right_value ^
          ") = EQUAL"
      | MLUnit =>
          choose (context_mode context)
            (fn () => "true")
            (fn () =>
              "let val _ = " ^ left_value ^ " val _ = " ^ right_value ^
              " in true end")
      | MLWord _ =>
          "IntInf.compare (" ^ left_value ^ ", " ^ right_value ^
          ") = EQUAL"
      | MLTuple [_, _] =>
          let
            val (hol_left, hol_right) = pairSyntax.dest_prod ty
            val eq_left = equality_name context hol_left
            val eq_right = equality_name context hol_right
          in
            "(case (" ^ left_value ^ ", " ^ right_value ^ ") of " ^
            "((a1, a2), (b1, b2)) => " ^ eq_left ^ " a1 b1 andalso " ^
            eq_right ^ " a2 b2)"
          end
      (* [MLList] cannot arise in lazy mode: [classify_primitive] routes
         lists, options, tuples and strings through [algebraic], which is
         [NONE] there, so a lazy list is an [MLSusp] of a generated
         datatype and lands in [MLDatatype] below.  [left_value] and
         [right_value] are therefore the identifiers [x] and [y] here, as
         [force] is the identity in strict mode.  [atom] still guards the
         two argument positions, so this arm does not silently become
         wrong if lazy mode ever grows a native list representation;
         [MLArrow] below solves the same problem by let-binding both
         sides first. *)
      | MLList _ =>
          let
            val element = listSyntax.dest_list_type ty
            val eq_element = equality_name context element
          in
            "let fun loop [] [] = true | loop (a :: as') (b :: bs') = " ^
            eq_element ^ " a b andalso loop as' bs' | loop _ _ = false " ^
            "in loop " ^ atom left_value ^ " " ^ atom right_value ^ " end"
          end
      | MLOption _ =>
          let
            val element = optionSyntax.dest_option ty
            val eq_element = equality_name context element
          in
            "(case (" ^ left_value ^ ", " ^ right_value ^ ") of " ^
            "(NONE, NONE) => true | (SOME a, SOME b) => " ^
            eq_element ^ " a b | _ => false)"
          end
      | MLArrow _ =>
          let
            val (domain_ty, range_ty) = Type.dom_rng ty
            val eq_range = equality_name context range_ty
            fun body left_fun right_fun =
              "List.all (fn z => " ^ eq_range ^ " (" ^ left_fun ^ " z) (" ^
              right_fun ^ " z)) " ^
              parens (enum_expression context domain_ty)
          in
            choose (context_mode context)
              (fn () => body left right)
              (fn () =>
                "let val left_fun = " ^ left_value ^
                " val right_fun = " ^ right_value ^ " in " ^
                body "left_fun" "right_fun" ^ " end")
          end
      | MLDatatype _ => datatype_equality context ty left right
      | MLVar _ =>
          reject ("cannot generate structural equality for type variable " ^
                  type_name ty)
      | MLTuple _ => raise Fail "Refute_Extract: malformed tuple type"
      | MLSusp _ => raise Fail "Refute_Extract: nested lazy type"
    end

  and datatype_equality context ty left right =
    let
      val force = #force (context_operations context)
      val info =
        case lookup_datatype context ty of
          SOME found => found
        | NONE => raise Fail "Refute_Extract: missing datatype"
      fun variables prefix count =
        List.tabulate (count, fn index =>
          prefix ^ Int.toString (index + 1))
      fun payload name [] = name
        | payload name [variable] = name ^ " " ^ variable
        | payload name vars = name ^ " (" ^ join ", " vars ^ ")"
      fun clause (_, arguments, name) =
        let
          val avars = variables "a" (length arguments)
          val bvars = variables "b" (length arguments)
          val comparisons = ListPair.mapEq (fn (arg_ty, (a, b)) =>
            equality_name context arg_ty ^ " " ^ a ^ " " ^ b)
            (arguments, ListPair.zip (avars, bvars))
          val body = if null comparisons then "true"
                     else join " andalso " comparisons
        in
          "(" ^ payload name avars ^ ", " ^ payload name bvars ^
          ") => " ^ body
        end
    in
      "(case (" ^ force left ^ ", " ^ force right ^ ") of " ^
      join " | " (List.map clause (#constructors info)) ^
      " | _ => false)"
    end

  fun equality_declarations context =
    let
      fun discover seen =
        case List.find (fn ty =>
          not (Util.member_type ty seen))
          (!(#equalities context)) of
            NONE => ()
          | SOME ty =>
              (ignore (equality_body context ty "x" "y");
               discover (ty :: seen))
      fun one keyword (ty, mlty, name) =
        keyword ^ " " ^ name ^ " (x : " ^ ml_ty_text mlty ^ ") " ^
        "(y : " ^ ml_ty_text mlty ^ ") =\n  " ^
        equality_body context ty "x" "y"
      fun declarations types =
        case types of
            [] => ""
          | first :: rest =>
              join "\n" (one "fun" first :: List.map (one "and") rest) ^
              "\n"
      (* Only a requested equality is declared, in either mode.  Emitting one
         per registered type would make a representation-only compilation,
         or any compilation that merely mentions a function type, fail on an
         equality nobody asked for: [equality_body] on an arrow has to
         enumerate its domain. *)
      val _ = discover []
      val requested = !(#equalities context)
      val types = List.filter (fn (ty, _, _) =>
        Util.member_type ty requested)
        (rev (!(#types context)))
    in
      declarations types
    end

  val prelude =
    "fun refute_num_sub a b = if a < b then 0 else a - b\n" ^
    "fun refute_nonzero who b =\n" ^
    "  if b = 0 then raise Refute_EvalSML.Stuck who else b\n" ^
    "fun refute_num_div a b = if b = 0 then 0 else IntInf.div (a, b)\n" ^
    "fun refute_num_mod a b = if b = 0 then a else IntInf.mod (a, b)\n" ^
    "fun refute_int_div a b =\n" ^
    "  IntInf.div (a, refute_nonzero \"int_div 0\" b)\n" ^
    "fun refute_int_mod a b =\n" ^
    "  IntInf.mod (a, refute_nonzero \"int_mod 0\" b)\n" ^
    "fun refute_int_quot a b =\n" ^
    "  IntInf.quot (a, refute_nonzero \"int_quot 0\" b)\n" ^
    "fun refute_int_rem a b =\n" ^
    "  IntInf.rem (a, refute_nonzero \"int_rem 0\" b)\n" ^
    "fun refute_pow a n =\n" ^
    "  if n = 0 then 1 else if IntInf.mod (n, 2) = 0 then\n" ^
    "    let val p = refute_pow a (IntInf.div (n, 2)) in p * p end\n" ^
    "  else a * refute_pow a (n - 1)\n" ^
    "fun refute_norm width value =\n" ^
    "  IntInf.mod (value, IntInf.pow (2, width))\n" ^
    "fun refute_signed width value =\n" ^
    "  let val modulus = IntInf.pow (2, width)\n" ^
    "      val normalized = IntInf.mod (value, modulus)\n" ^
    "  in if normalized < IntInf.div (modulus, 2) then normalized\n" ^
    "     else normalized - modulus end\n" ^
    "fun refute_hd [] = raise Refute_EvalSML.Stuck \"HD []\"\n" ^
    "  | refute_hd (x :: _) = x\n" ^
    "fun refute_tl [] = []\n" ^
    "  | refute_tl (_ :: xs) = xs\n" ^
    "fun refute_the NONE = raise Refute_EvalSML.Stuck \"THE NONE\"\n" ^
    "  | refute_the (SOME x) = x\n" ^
    "fun refute_chr n =\n" ^
    "  if n < 0 orelse n >= 256 then\n" ^
    "    raise Refute_EvalSML.Stuck \"CHR out of range\"\n" ^
    "  else Char.chr (IntInf.toInt n)\n" ^
    "fun refute_nth xs n =\n" ^
    "  (List.nth (xs, IntInf.toInt n)\n" ^
    "   handle Interrupt => raise Interrupt\n" ^
    "        | _ => raise Refute_EvalSML.Stuck \"EL\")\n" ^
    "fun refute_foldr f z [] = z\n" ^
    "  | refute_foldr f z (x :: xs) = f x (refute_foldr f z xs)\n" ^
    "fun refute_foldl f z [] = z\n" ^
    "  | refute_foldl f z (x :: xs) = refute_foldl f (f z x) xs\n" ^
    "fun refute_all_distinct eq xs =\n" ^
    "  let fun member x = List.exists (fn y => eq x y)\n" ^
    "      fun loop [] = true\n" ^
    "        | loop (x :: rest) = not (member x rest) andalso loop rest\n" ^
    "  in loop xs end\n" ^
    "fun refute_word_div width a b =\n" ^
    "  refute_norm width (refute_num_div a b)\n" ^
    "fun refute_word_mod width a b =\n" ^
    "  refute_norm width (refute_num_mod a b)\n" ^
    "fun refute_word_quot width a b =\n" ^
    "  if refute_norm width b = 0 then 0 else refute_norm width\n" ^
    "    (refute_int_quot (refute_signed width a)\n" ^
    "      (refute_signed width b))\n" ^
    "fun refute_word_rem width a b =\n" ^
    "  if refute_norm width b = 0 then refute_norm width a else\n" ^
    "    refute_norm width (refute_int_rem (refute_signed width a)\n" ^
    "      (refute_signed width b))\n" ^
    "fun refute_shift amount =\n" ^
    "  (Word.fromInt (IntInf.toInt amount)\n" ^
    "   handle Interrupt => raise Interrupt\n" ^
    "        | _ => raise Refute_EvalSML.Stuck \"word shift\")\n" ^
    (* the guard keeps the shift from materializing an enormous integer
       that refute_norm would immediately reduce to 0 *)
    "fun refute_word_lsl width value amount =\n" ^
    "  if amount >= IntInf.fromInt width then 0\n" ^
    "  else refute_norm width (IntInf.<< (value, refute_shift amount))\n" ^
    "fun refute_word_lsr width value amount =\n" ^
    "  if amount >= IntInf.fromInt width then 0\n" ^
    "  else IntInf.~>> (refute_norm width value, refute_shift amount)\n" ^
    "fun refute_word_asr width value amount =\n" ^
    "  if amount >= IntInf.fromInt width then\n" ^
    "    if refute_signed width value < 0 then refute_norm width ~1 else 0\n" ^
    "  else refute_norm width\n" ^
    "    (IntInf.~>> (refute_signed width value, refute_shift amount))\n" ^
    "fun refute_last [] = raise Refute_EvalSML.Stuck \"LAST []\"\n" ^
    "  | refute_last [x] = x\n" ^
    "  | refute_last (_ :: xs) = refute_last xs\n" ^
    "fun refute_front [] = []\n" ^
    "  | refute_front [_] = []\n" ^
    "  | refute_front (x :: xs) = x :: refute_front xs\n"

  fun lookup_definition ({definitions, ...} : context) constant =
    List.find (fn (other, _, _, _) => same_term other constant)
      (!definitions)

  fun lookup_pending ({pending, ...} : context) constant =
    List.exists (same_term constant) (!pending)

  fun equations_of theorem =
    let
      fun split tm =
        let val (_, body) = boolSyntax.strip_forall tm
        in
          case Lib.total boolSyntax.dest_conj body of
            SOME (left, right) => split left @ split right
          | NONE => [body]
        end
    in
      split (Thm.concl theorem)
    end

  (* The callable arity of an emitted definition is the number of arguments
     on its equation lhs, not the number of arrows in the constant's type.
     They differ for function-valued definitions such as
     [UNIV = (\x. T)].  Cache that arity with the definition so every strict
     and lazy call uses the same convention as its emitted clauses. *)
  fun definition_equations constant theorem =
    let
      fun equation tm =
        let
          val (left, right) = boolSyntax.dest_eq tm
            handle Feedback.HOL_ERR _ =>
              reject ("non-equational rule for " ^
                      kname_text (kname constant))
          val (head, arguments) = boolSyntax.strip_comb left
          val _ =
            if Term.is_const head andalso Term.same_const head constant then ()
            else reject ("rule has the wrong head for " ^
                         kname_text (kname constant))
        in
          (arguments, right)
        end
      val equations = List.map equation (equations_of theorem)
      val _ = if null equations then
        reject ("definition has no clauses for " ^
                kname_text (kname constant)) else ()
      val arity = length (#1 (hd equations))
      val _ = if List.all (fn (arguments, _) =>
        length arguments = arity) equations then ()
        else reject ("definition has inconsistent arities for " ^
                     kname_text (kname constant))
    in
      equations
    end

  fun definition_arity constant theorem =
    length (#1 (hd (definition_equations constant theorem)))

  fun theorem_for_typebase constant =
    let
      fun has_head theorem = List.exists (fn equation =>
        case Lib.total boolSyntax.dest_eq equation of
          SOME (left, _) =>
            let val (head, _) = boolSyntax.strip_comb left
            in Term.is_const head andalso Term.same_const head constant end
        | NONE => false) (equations_of theorem)
      fun from_info info =
        let
          val theorems =
            (TypeBasePure.accessors_of info @ TypeBasePure.updates_of info @
             [TypeBasePure.case_def_of info])
            handle Feedback.HOL_ERR _ =>
              TypeBasePure.accessors_of info @ TypeBasePure.updates_of info
        in
          List.find has_head theorems
        end
    in
      Lib.get_first from_info (TypeBase.elts ())
    end

  fun compset_items ({compset_items = items, ...} : context) =
    case !items of
      SOME listing => listing
    | NONE =>
        let
          val listing = computeLib.listItems (computeLib.the_compset ())
          val _ = items := SOME listing
        in
          listing
        end

  fun theorem_for_compset context constant =
    let
      val (thy, name) = kname constant
      val item = List.find (fn ((entry_name, entry_thy), _) =>
        entry_name = name andalso entry_thy = thy)
        (compset_items context)
    in
      case item of
        NONE => NONE
      | SOME (_, transforms) =>
          let
            val rules = List.concat (List.map (fn transform =>
              case transform of
                clauses.RRules theorems => theorems
              | clauses.Conversion _ => []) transforms)
            val has_conversion = List.exists (fn transform =>
              case transform of clauses.Conversion _ => true | _ => false)
              transforms
          in
            if has_conversion then
              reject ("compset conversion is not extractable for " ^
                      kname_text (kname constant))
            else if List.exists (not o null o Thm.hyp) rules then
              reject ("conditional compset rule for " ^
                      kname_text (kname constant))
            else if List.exists (fn theorem =>
              List.exists (fn equation =>
                case Lib.total boolSyntax.dest_eq equation of
                  SOME (left, _) =>
                    Option.isSome (Lib.total Type.dom_rng
                      (Term.type_of left))
                | NONE => true) (equations_of theorem)) rules then
              reject ("lazy or non-equational compset rule for " ^
                      kname_text (kname constant))
            else
              case rules of
                [] => NONE
              | first :: rest =>
                  SOME (List.foldl (fn (theorem, result) =>
                    Thm.CONJ result theorem) first rest)
          end
    end

  fun definition_theorem context constant =
    case DefnBase.lookup_userdef constant of
      SOME {const, thm = DefnBase.STDEQNS theorem, ...} =>
        let
          val theta = Type.match_type (Term.type_of const)
            (Term.type_of constant)
        in
          Thm.INST_TYPE theta theorem
        end
    | SOME {thm = DefnBase.OTHER _, ...} =>
        reject ("non-equational definition for " ^
                kname_text (kname constant))
    | NONE =>
        (case theorem_for_typebase constant of
           SOME theorem => theorem
         | NONE =>
             (case theorem_for_compset context constant of
                SOME theorem => theorem
              | NONE =>
                  reject ("no extractable equations for constant " ^
                          kname_text (kname constant))))

  fun mutual_constants constant =
    case (DefnBase.lookup_userdef constant,
          DefnBase.lookup_indn constant) of
      (SOME {const = generic, ...}, SOME (_, names)) =>
        let
          val theta = Type.match_type (Term.type_of generic)
            (Term.type_of constant)
          fun instantiate name = Term.inst theta (Term.prim_mk_const name)
        in
          List.map instantiate names
        end
    | _ => [constant]

  fun ensure_definition context constant =
    case lookup_definition context constant of
      SOME (_, name, _, _) => name
    | NONE =>
        if lookup_pending context constant then
          let val (_, name) = kname constant
          in
            case List.find (fn (other, _, _, _) =>
              Term.same_const other constant)
              (!(#definitions context)) of
              SOME (_, mlname, _, _) => mlname
            | NONE => lower_name name
          end
        else
          let
            val group = mutual_constants constant
            fun register member =
              case lookup_definition context member of
                SOME item => item
              | NONE =>
                  let
                    val (_, base) = kname member
                    val theorem = definition_theorem context member
                    val item = (member, fresh_const context base,
                                definition_arity member theorem, theorem)
                    val _ = #definitions context :=
                      item :: !(#definitions context)
                    val _ = #pending context :=
                      member :: !(#pending context)
                  in
                    item
                  end
            val registered = List.map register group
            val registered_constants = List.map #1 registered
            val _ = #definition_groups context :=
              registered_constants :: !(#definition_groups context)
          in
            case lookup_definition context constant of
              SOME (_, name, _, _) => name
            | NONE =>
                reject ("mutual definition group omitted " ^
                        kname_text (kname constant))
          end

  fun type_key ty =
    case Lib.total Type.dest_vartype ty of
        SOME name => "var:" ^ name
      | NONE =>
          let val {Thy, Tyop, Args} = Type.dest_thy_type ty
          in
            "op:" ^ Thy ^ ":" ^ Tyop ^ "[" ^
            String.concatWith "," (List.map type_key Args) ^ "]"
          end

  (* HOL variables are identified by both name and type.  The latter matters
     even when their extracted SML representations coincide, e.g. [num] and
     [int] are both [IntInf.int]. *)
  fun variable_name variable =
    let val (name, ty) = Term.dest_var variable
    in clean_name (name ^ "\000" ^ type_key ty) end

  fun with_arity arguments arity build =
    let
      val supplied = length arguments
      val used = Int.min (supplied, arity)
      val initial = List.take (arguments, used)
      val extra = List.drop (arguments, used)
      val missing = arity - used
      val variables = List.tabulate (missing, fn index =>
        "refute_arg_" ^ Int.toString index)
      val body = build (initial @ variables)
      (* An under-applied primitive compiles to an abstraction, and a bare
         [fn x => ...] is legal in neither the head nor the argument of an
         application.  Bracket it here, once, so that no splice site has to
         know that [with_arity] can hand it one. *)
      val abstraction =
        if null variables then body
        else parens (List.foldr (fn (variable, result) =>
          "fn " ^ variable ^ " => " ^ result) body variables)
    in
      List.foldl (fn (argument, result) =>
        parens (result ^ " " ^ parens argument)) abstraction extra
    end

  (* A lazy expression denotes one suspension, never a suspension of a
     suspension.  When an ML computation returns a lazy value, defer the
     computation and flatten its result under the new outer suspension.
     This is the composition operation used by applications and
     eliminators: merely constructing a surrounding constructor must not
     run either of them. *)
  fun constructor_expression context constructor arguments =
    let
      val ops = context_operations context
      val delay = #delay ops
      val apply = #apply ops
      val (argument_types, _) =
        boolSyntax.strip_fun (Term.type_of constructor)
      val arity = length argument_types
      fun custom name values =
        case values of
          [] => name
        | [argument] => name ^ " " ^ parens argument
        | _ => name ^ " " ^ parens (join ", " values)
      fun lazy_custom name =
        let
          fun abstract [] body = body
            | abstract (variable :: variables) body =
                delay ("fn " ^ variable ^ " => " ^
                  abstract variables body)
          val supplied = Int.min (length arguments, arity)
          val initial = List.take (arguments, supplied)
          val extra = List.drop (arguments, supplied)
          val variables = List.tabulate (arity - supplied, fn index =>
            "refute_arg_" ^ Int.toString index)
          val built = delay (custom name (initial @ variables))
          val abstraction = abstract variables built
        in
          List.foldl (fn (argument, result) =>
            apply result argument) abstraction extra
        end
      fun strict_custom name = with_arity arguments arity (custom name)
      fun strict () =
        case kname constructor of
            ("list", "NIL") =>
              if is_char_list (#2 (boolSyntax.strip_fun
                (Term.type_of constructor))) then quote "" else "[]"
          | ("list", "CONS") => with_arity arguments 2 (fn values =>
              case values of
                [head, tail] =>
                  if is_char_list (#2 (boolSyntax.strip_fun
                    (Term.type_of constructor))) then
                    parens ("String.str " ^ parens head ^ " ^ " ^ tail)
                  else parens (head ^ " :: " ^ tail)
              | _ => raise Fail "CONS")
          | ("option", "NONE") => "NONE"
          | ("option", "SOME") => with_arity arguments 1 (fn values =>
              case values of [argument] => "SOME " ^ parens argument
              | _ => raise Fail "SOME")
          | ("pair", ",") => with_arity arguments 2 (fn values =>
              parens (join ", " values))
          | _ =>
              (case constructor_for context constructor of
                   SOME (_, _, name) => strict_custom name
                 | NONE => reject ("unknown constructor " ^
                                   kname_text (kname constructor)))
      fun lazy () =
        case constructor_for context constructor of
            SOME (_, _, name) => lazy_custom name
          | NONE => reject ("unknown lazy constructor " ^
                            kname_text (kname constructor))
    in
      choose (context_mode context) strict lazy
    end

  fun pattern context term =
    if Term.is_var term then variable_name term
    else if Literal.is_numeral term then
      parens (Arbnum.toString (Literal.relaxed_dest_numeral term) ^
              " : IntInf.int")
    else if intSyntax.is_int_literal term then
      let
        val text = Arbint.toString (intSyntax.int_of_term term)
        val decimal = String.substring (text, 0, String.size text - 1)
        val sml_decimal = if String.isPrefix "-" decimal then
          "~" ^ String.extract (decimal, 1, NONE) else decimal
      in parens (sml_decimal ^ " : IntInf.int") end
    else if Term.aconv term boolSyntax.T then "true"
    else if Term.aconv term boolSyntax.F then "false"
    else if Literal.is_char_lit term then
      "#" ^ quote (String.str (Literal.dest_char_lit term))
    else if Literal.is_string_lit term then
      quote (Literal.relaxed_dest_string_lit term)
    else if oneSyntax.is_one term then "()"
    else
      let
        val (head, arguments) = boolSyntax.strip_comb term
      in
        if Term.is_const head andalso TypeBase.is_constructor head then
          choose (context_mode context)
            (fn () => constructor_expression context head
              (List.map (pattern context) arguments))
            (fn () =>
              case constructor_for context head of
                  SOME (_, _, name) =>
                    (* Unreachable today: [pattern] is only called from the
                       strict let, paired-abstraction, case and definition
                       compilers.  A nested constructor pattern would
                       otherwise be spliced as [C1 C2 x]. *)
                    (case List.map (pattern context) arguments of
                         [] => name
                       | [argument] => name ^ " " ^ atom argument
                       | values => name ^ " (" ^ join ", " values ^ ")")
                | NONE => reject ("unknown lazy pattern constructor " ^
                                  kname_text (kname head)))
        else
          reject ("non-constructor pattern: " ^
                  Parse.term_to_string term)
      end

  fun binary operator arguments = with_arity arguments 2 (fn values =>
    case values of [left, right] => parens (left ^ " " ^ operator ^ " " ^
      right) | _ => raise Fail "binary")

  fun call name arity arguments = with_arity arguments arity (fn values =>
    parens (name ^ " " ^ join " " (List.map parens values)))

  fun record_primitive context head arguments =
    let
      fun find_field info =
        let
          val fields = TypeBasePure.fields_of info
          fun matching (index, (_, {accessor, fupd, ...})) =
            if Term.same_const accessor head then SOME (false, index)
            else if Term.same_const fupd head then SOME (true, index)
            else NONE
        in
          case Lib.get_first matching (Lib.enumerate 0 fields) of
            SOME match => SOME (info, fields, match)
          | NONE => NONE
        end
    in
      case Lib.get_first find_field (TypeBase.elts ()) of
        NONE => NONE
      | SOME (info, fields, (is_update, selected)) =>
          let
            val generic_ty = TypeBasePure.ty_of info
            val generic_head = if is_update then
              #fupd (#2 (List.nth (fields, selected)))
              else #accessor (#2 (List.nth (fields, selected)))
            val theta = Type.match_type (Term.type_of generic_head)
              (Term.type_of head)
            val record_ty = Type.type_subst theta generic_ty
            val _ = ignore (ensure_type context record_ty)
            val datatype_info = valOf (lookup_datatype context record_ty)
            val (_, field_types, constructor_name) =
              hd (#constructors datatype_info)
            val variables = List.tabulate (length field_types, fn index =>
              "field_" ^ Int.toString index)
            fun payload values =
              case values of
                [value] => value
              | _ => parens (join ", " values)
            fun record_pattern name =
              constructor_name ^ " " ^ payload variables ^ " => " ^ name
            fun accessor values =
              case values of
                [record] =>
                  parens ("case " ^ record ^ " of " ^
                    record_pattern (List.nth (variables, selected)))
              | _ => raise Fail "record accessor"
            fun updater values =
              case values of
                [update, record] =>
                  let
                    val new_fields = List.map (fn (index, variable) =>
                      if index = selected then
                        parens (parens update ^ " " ^ variable)
                      else variable) (Lib.enumerate 0 variables)
                    val rebuilt = constructor_name ^ " " ^
                      payload new_fields
                  in
                    parens ("case " ^ record ^ " of " ^
                      record_pattern rebuilt)
                  end
              | _ => raise Fail "record updater"
          in
            SOME (if is_update then with_arity arguments 2 updater
                  else with_arity arguments 1 accessor)
          end
    end

  fun word_result_width head arguments =
    let
      val result = #2 (boolSyntax.strip_fun (Term.type_of head))
    in
      if wordsSyntax.is_word_type result then word_width result
      else
        case arguments of
          argument :: _ => word_width (Term.type_of argument)
        | [] => reject ("word primitive has no concrete width: " ^
                        kname_text (kname head))
    end

  fun strict_primitive context head argument_terms arguments =
    let
      val key = kname head
      fun num_binary operator = binary operator arguments
      fun norm_binary operator =
        let val width = word_result_width head argument_terms
        in
          with_arity arguments 2 (fn values =>
            case values of
              [left, right] =>
                "refute_norm " ^ Int.toString width ^ " " ^
                parens (left ^ " " ^ operator ^ " " ^ right)
            | _ => raise Fail "norm_binary")
        end
      fun compare signed operator =
        let val width = word_result_width head argument_terms
            fun side value = if signed then
              "refute_signed " ^ Int.toString width ^ " " ^ parens value
              else value
        in
          with_arity arguments 2 (fn values =>
            case values of [left, right] =>
              parens (side left ^ " " ^ operator ^ " " ^ side right)
            | _ => raise Fail "compare")
        end
      fun argument_types () = #1 (boolSyntax.strip_fun (Term.type_of head))
      fun list_domain () = #1 (Type.dom_rng (Term.type_of head))
      fun string_list () = is_char_list (list_domain ())
      fun string_argument index =
        is_char_list (List.nth (argument_types (), index))
      fun list_eq_argument () =
        let val element = listSyntax.dest_list_type (list_domain ())
        in equality_name context element end
    in
      (* The key table covers the common intrinsics; the record scan over
         TypeBase runs only when nothing in the table matches. *)
      case key of
        ("bool", "T") => SOME "true"
      | ("bool", "ARB") =>
          SOME "(raise Refute_EvalSML.Stuck \"ARB\")"
      | ("bool", "F") => SOME "false"
      | ("bool", "~") => SOME (call "not" 1 arguments)
      | ("bool", "/\\") => SOME (binary "andalso" arguments)
      | ("bool", "\\/") => SOME (binary "orelse" arguments)
      | ("min", "==>") => SOME (with_arity arguments 2 (fn values =>
          case values of [left, right] =>
            parens ("not " ^ parens left ^ " orelse " ^ right)
          | _ => raise Fail "implication"))
      | ("min", "=") =>
          let val compared = #1 (Type.dom_rng (Term.type_of head))
          in SOME (call (equality_name context compared) 2 arguments) end
      | ("num", "0") => SOME (num_literal Arbnum.zero)
      | ("arithmetic", "ZERO") => SOME (num_literal Arbnum.zero)
      | ("arithmetic", "NUMERAL") => SOME (call "(fn x => x)" 1 arguments)
      | ("arithmetic", "BIT1") => SOME (with_arity arguments 1 (fn values =>
          case values of [value] => parens ("2 * " ^ value ^ " + 1")
          | _ => raise Fail "BIT1"))
      | ("arithmetic", "BIT2") => SOME (with_arity arguments 1 (fn values =>
          case values of [value] => parens ("2 * " ^ value ^ " + 2")
          | _ => raise Fail "BIT2"))
      | ("num", "SUC") => SOME (with_arity arguments 1 (fn values =>
          case values of [value] => parens (value ^ " + 1")
          | _ => raise Fail "SUC"))
      | ("prim_rec", "PRE") => SOME (with_arity arguments 1 (fn values =>
          case values of [value] =>
            parens ("if " ^ value ^ " = 0 then 0 else " ^ value ^ " - 1")
          | _ => raise Fail "PRE"))
      | ("arithmetic", "+") => SOME (num_binary "+")
      | ("arithmetic", "-") => SOME (call "refute_num_sub" 2 arguments)
      | ("arithmetic", "*") => SOME (num_binary "*")
      | ("arithmetic", "DIV") => SOME (call "refute_num_div" 2 arguments)
      | ("arithmetic", "MOD") => SOME (call "refute_num_mod" 2 arguments)
      | ("arithmetic", "EXP") => SOME (call "refute_pow" 2 arguments)
      | ("prim_rec", "<") => SOME (num_binary "<")
      | ("arithmetic", "<=") => SOME (num_binary "<=")
      | ("arithmetic", ">") => SOME (num_binary ">")
      | ("arithmetic", ">=") => SOME (num_binary ">=")
      | ("arithmetic", "MIN") => SOME (with_arity arguments 2 (fn values =>
          case values of [a, b] => parens ("if " ^ a ^ " < " ^ b ^
            " then " ^ a ^ " else " ^ b)
          | _ => raise Fail "MIN"))
      | ("arithmetic", "MAX") => SOME (with_arity arguments 2 (fn values =>
          case values of [a, b] => parens ("if " ^ a ^ " < " ^ b ^
            " then " ^ b ^ " else " ^ a)
          | _ => raise Fail "MAX"))
      | ("arithmetic", "EVEN") => SOME (with_arity arguments 1 (fn values =>
          case values of [a] => "IntInf.mod (" ^ a ^ ", 2) = 0"
          | _ => raise Fail "EVEN"))
      | ("arithmetic", "ODD") => SOME (with_arity arguments 1 (fn values =>
          case values of [a] => "IntInf.mod (" ^ a ^ ", 2) = 1"
          | _ => raise Fail "ODD"))
      | ("arithmetic", "DIV2") => SOME (with_arity arguments 1 (fn values =>
          case values of [a] => "IntInf.div (" ^ a ^ ", 2)"
          | _ => raise Fail "DIV2"))
      | ("integer", "int_neg") => SOME (with_arity arguments 1 (fn values =>
          case values of [a] => parens ("~" ^ parens a)
          | _ => raise Fail "int_neg"))
      | ("integer", "int_add") => SOME (binary "+" arguments)
      | ("integer", "int_sub") => SOME (binary "-" arguments)
      | ("integer", "int_mul") => SOME (binary "*" arguments)
      | ("integer", "int_exp") => SOME (call "refute_pow" 2 arguments)
      | ("integer", "int_div") => SOME (call "refute_int_div" 2 arguments)
      | ("integer", "int_mod") => SOME (call "refute_int_mod" 2 arguments)
      | ("integer", "int_quot") => SOME (call "refute_int_quot" 2 arguments)
      | ("integer", "int_rem") => SOME (call "refute_int_rem" 2 arguments)
      | ("integer", "int_lt") => SOME (binary "<" arguments)
      | ("integer", "int_le") => SOME (binary "<=" arguments)
      | ("integer", "int_gt") => SOME (binary ">" arguments)
      | ("integer", "int_ge") => SOME (binary ">=" arguments)
      | ("integer", "ABS") => SOME (call "IntInf.abs" 1 arguments)
      | ("integer", "int_min") => SOME (with_arity arguments 2 (fn values =>
          case values of [a, b] => parens ("if " ^ a ^ " < " ^ b ^
            " then " ^ a ^ " else " ^ b) | _ => raise Fail "int_min"))
      | ("integer", "int_max") => SOME (with_arity arguments 2 (fn values =>
          case values of [a, b] => parens ("if " ^ a ^ " < " ^ b ^
            " then " ^ b ^ " else " ^ a) | _ => raise Fail "int_max"))
      | ("integer", "int_of_num") => SOME (call "(fn x => x)" 1 arguments)
      | ("integer", "Num") => SOME (call "IntInf.abs" 1 arguments)
      | ("combin", "I") => SOME (call "(fn x => x)" 1 arguments)
      | ("combin", "K") => SOME (with_arity arguments 2 (fn values =>
          case values of [left, _] => left | _ => raise Fail "K"))
      | ("combin", "o") => SOME (with_arity arguments 3 (fn values =>
          case values of [f, g, x] => parens (atom f ^ " " ^ parens
            (atom g ^ " " ^ parens x)) | _ => raise Fail "o"))
      | ("combin", "UPDATE") =>
          let
            val domain = hd (#1 (boolSyntax.strip_fun
              (Term.type_of head)))
            val equality = equality_name context domain
          in
            SOME (with_arity arguments 3 (fn values =>
              case values of [point, value, base] =>
                parens ("fn refute_update_x => if " ^ equality ^
                  " refute_update_x " ^ atom point ^ " then " ^ value ^
                  " else " ^ atom base ^ " refute_update_x")
              | _ => raise Fail "UPDATE"))
          end
      | ("pair", "FST") => SOME (call "#1" 1 arguments)
      | ("pair", "SND") => SOME (call "#2" 1 arguments)
      | ("pair", "CURRY") => SOME (with_arity arguments 3 (fn values =>
          case values of [f, a, b] => atom f ^ " " ^ parens (a ^ ", " ^ b)
          | _ => raise Fail "CURRY"))
      | ("pair", "UNCURRY") => SOME (with_arity arguments 2 (fn values =>
          case values of [f, pair] => atom f ^ " " ^ parens pair
          | _ => raise Fail "UNCURRY"))
      | ("list", "NULL") => SOME (with_arity arguments 1 (fn values =>
          case values of [a] =>
            if string_list () then "String.size " ^ parens a ^ " = 0"
            else parens ("case " ^ a ^ " of [] => true | _ => false")
          | _ => raise Fail "NULL"))
      | ("list", "HD") => SOME (with_arity arguments 1 (fn values =>
          case values of [a] =>
            if string_list () then parens ("if String.size " ^ parens a ^
              " = 0 then raise Refute_EvalSML.Stuck \"HD []\" " ^
              "else " ^ Refute_EvalSML.char_list_head_source a)
            else "refute_hd " ^ parens a
          | _ => raise Fail "HD"))
      | ("list", "TL") => SOME (with_arity arguments 1 (fn values =>
          case values of [a] =>
            if string_list () then Refute_EvalSML.char_list_tail_source a
            else "refute_tl " ^ parens a
          | _ => raise Fail "TL"))
      | ("list", "APPEND") =>
          SOME (binary (if string_list () then "^" else "@") arguments)
      | ("list", "FLAT") => SOME (call
          (if is_char_list (listSyntax.dest_list_type (list_domain ())) then
             "String.concat"
           else "List.concat") 1 arguments)
      | ("list", "LENGTH") => SOME (with_arity arguments 1 (fn values =>
          case values of [a] =>
            "IntInf.fromInt (" ^
            (if string_list () then "String.size " else "List.length ") ^
            parens a ^ ")"
          | _ => raise Fail "LENGTH"))
      | ("list", "MAP") => SOME (with_arity arguments 2 (fn values =>
          case values of [f, xs] =>
            let
              val input = if string_argument 1 then
                "String.explode " ^ parens xs else xs
              val mapped = "List.map " ^ parens f ^ " " ^ parens input
              val result_ty = #2 (boolSyntax.strip_fun (Term.type_of head))
            in
              if is_char_list result_ty then
                "String.implode " ^ parens mapped else mapped
            end
          | _ => raise Fail "MAP"))
      | ("list", "FILTER") => SOME (with_arity arguments 2 (fn values =>
          case values of [f, xs] =>
            if string_argument 1 then
              "String.implode (List.filter " ^ parens f ^
              " (String.explode " ^ parens xs ^ "))"
            else "List.filter " ^ parens f ^ " " ^ parens xs
          | _ => raise Fail "FILTER"))
      | ("list", "EVERY") => SOME (with_arity arguments 2 (fn values =>
          case values of [f, xs] => "List.all " ^ parens f ^ " " ^
            parens (if string_argument 1 then
              "String.explode " ^ parens xs else xs)
          | _ => raise Fail "EVERY"))
      | ("list", "EXISTS") => SOME (with_arity arguments 2 (fn values =>
          case values of [f, xs] => "List.exists " ^ parens f ^ " " ^
            parens (if string_argument 1 then
              "String.explode " ^ parens xs else xs)
          | _ => raise Fail "EXISTS"))
      | ("list", "FOLDR") => SOME (with_arity arguments 3 (fn values =>
          case values of [f, z, xs] =>
            "refute_foldr " ^ atom f ^ " " ^ atom z ^ " " ^
            parens (if string_argument 2 then
              "String.explode " ^ parens xs else xs)
          | _ => raise Fail "FOLDR"))
      | ("list", "FOLDL") => SOME (with_arity arguments 3 (fn values =>
          case values of [f, z, xs] =>
            "refute_foldl " ^ atom f ^ " " ^ atom z ^ " " ^
            parens (if string_argument 2 then
              "String.explode " ^ parens xs else xs)
          | _ => raise Fail "FOLDL"))
      | ("list", "REVERSE") =>
          SOME (call (if string_list () then
            "(String.implode o List.rev o String.explode)" else "List.rev")
            1 arguments)
      | ("list", "EL") => SOME (with_arity arguments 2 (fn values =>
          case values of [n, xs] =>
            if string_argument 1 then
              "(String.sub (" ^ xs ^ ", IntInf.toInt " ^ atom n ^ ") " ^
              "handle Interrupt => raise Interrupt " ^
              "| _ => raise Refute_EvalSML.Stuck \"EL\")"
            else "refute_nth " ^ atom xs ^ " " ^ atom n
          | _ => raise Fail "EL"))
      | ("list", "LAST") =>
          SOME (call (if string_list () then
            "(refute_last o String.explode)" else "refute_last")
            1 arguments)
      | ("list", "FRONT") =>
          SOME (call (if string_list () then
            "(String.implode o refute_front o String.explode)"
            else "refute_front") 1 arguments)
      | ("list", "SNOC") => SOME (with_arity arguments 2 (fn values =>
          case values of [x, xs] =>
            if string_argument 1 then
              parens (xs ^ " ^ String.str " ^ parens x)
            else parens (xs ^ " @ [" ^ x ^ "]")
          | _ => raise Fail "SNOC"))
      | ("list", "ALL_DISTINCT") =>
          SOME (with_arity arguments 1 (fn values =>
            case values of [xs] =>
              "refute_all_distinct " ^ list_eq_argument () ^ " " ^
              parens (if string_list () then
                "String.explode " ^ parens xs else xs)
            | _ => raise Fail "ALL_DISTINCT"))
      | ("option", "THE") => SOME (call "refute_the" 1 arguments)
      | ("option", "IS_SOME") => SOME (with_arity arguments 1 (fn values =>
          case values of [a] => parens ("case " ^ a ^
            " of SOME _ => true | NONE => false")
          | _ => raise Fail "IS_SOME"))
      | ("option", "IS_NONE") => SOME (with_arity arguments 1 (fn values =>
          case values of [a] => parens ("case " ^ a ^
            " of NONE => true | SOME _ => false")
          | _ => raise Fail "IS_NONE"))
      | ("option", "OPTION_MAP") => SOME (call "Option.map" 2 arguments)
      | ("option", "OPTION_JOIN") => SOME (with_arity arguments 1 (fn values =>
          case values of [value] => parens ("case " ^ value ^
            " of NONE => NONE | SOME x => x")
          | _ => raise Fail "OPTION_JOIN"))
      | ("string", "CHR") => SOME (call "refute_chr" 1 arguments)
      | ("string", "ORD") => SOME (with_arity arguments 1 (fn values =>
          case values of [a] => "IntInf.fromInt (Char.ord " ^ parens a ^
            ")" | _ => raise Fail "ORD"))
      | ("string", "EXPLODE") => SOME (call "(fn x => x)" 1 arguments)
      | ("string", "IMPLODE") => SOME (call "(fn x => x)" 1 arguments)
      | ("string", "DEST_STRING") =>
          SOME (with_arity arguments 1 (fn values =>
            case values of [value] => parens ("if String.size " ^
              parens value ^ " = 0 then NONE else SOME (" ^
              Refute_EvalSML.char_list_head_source value ^ ", " ^
              Refute_EvalSML.char_list_tail_source value ^ ")")
            | _ => raise Fail "DEST_STRING"))
      | ("string", "string_lt") => SOME (binary "<" arguments)
      | ("string", "string_le") => SOME (binary "<=" arguments)
      | ("string", "string_gt") => SOME (binary ">" arguments)
      | ("string", "string_ge") => SOME (binary ">=" arguments)
      | ("string", "char_lt") => SOME (binary "<" arguments)
      | ("string", "char_le") => SOME (binary "<=" arguments)
      | ("string", "char_gt") => SOME (binary ">" arguments)
      | ("string", "char_ge") => SOME (binary ">=" arguments)
      | ("words", "n2w") =>
          let val width = word_result_width head argument_terms
          in SOME (call ("refute_norm " ^ Int.toString width) 1 arguments) end
      | ("words", "w2n") => SOME (call "(fn x => x)" 1 arguments)
      | ("words", "word_add") => SOME (norm_binary "+")
      | ("words", "word_sub") => SOME (norm_binary "-")
      | ("words", "word_mul") => SOME (norm_binary "*")
      | ("words", "word_exp") =>
          let val width = word_result_width head argument_terms
          in SOME (with_arity arguments 2 (fn values =>
            case values of [a, b] => "refute_norm " ^ Int.toString width ^
              " (refute_pow " ^ atom a ^ " " ^ atom b ^ ")"
            | _ => raise Fail "word_exp")) end
      | ("words", "word_1comp") =>
          let val width = word_result_width head argument_terms
          in SOME (with_arity arguments 1 (fn values =>
            case values of [a] => "refute_norm " ^ Int.toString width ^
              " (IntInf.notb " ^ atom a ^ ")"
            | _ => raise Fail "word_1comp")) end
      | ("words", "word_2comp") =>
          let val width = word_result_width head argument_terms
          in SOME (with_arity arguments 1 (fn values =>
            case values of [a] => "refute_norm " ^ Int.toString width ^
              " (~" ^ parens a ^ ")"
            | _ => raise Fail "word_2comp")) end
      | ("words", "word_and") => SOME (with_arity arguments 2 (fn values =>
          case values of [a, b] => "IntInf.andb (" ^ a ^ ", " ^ b ^ ")"
          | _ => raise Fail "word_and"))
      | ("words", "word_or") => SOME (with_arity arguments 2 (fn values =>
          case values of [a, b] => "IntInf.orb (" ^ a ^ ", " ^ b ^ ")"
          | _ => raise Fail "word_or"))
      | ("words", "word_xor") => SOME (with_arity arguments 2 (fn values =>
          case values of [a, b] => "IntInf.xorb (" ^ a ^ ", " ^ b ^ ")"
          | _ => raise Fail "word_xor"))
      | ("words", "word_div") =>
          let val width = word_result_width head argument_terms
          in SOME (call ("refute_word_div " ^ Int.toString width)
            2 arguments) end
      | ("words", "word_mod") =>
          let val width = word_result_width head argument_terms
          in SOME (call ("refute_word_mod " ^ Int.toString width)
            2 arguments) end
      | ("words", "word_quot") =>
          let val width = word_result_width head argument_terms
          in SOME (call ("refute_word_quot " ^ Int.toString width)
            2 arguments) end
      | ("words", "word_rem") =>
          let val width = word_result_width head argument_terms
          in SOME (call ("refute_word_rem " ^ Int.toString width)
            2 arguments) end
      | ("words", "word_lsl") =>
          let val width = word_result_width head argument_terms
          in SOME (call ("refute_word_lsl " ^ Int.toString width)
            2 arguments) end
      | ("words", "word_lsr") =>
          let val width = word_result_width head argument_terms
          in SOME (call ("refute_word_lsr " ^ Int.toString width)
            2 arguments) end
      | ("words", "word_asr") =>
          let val width = word_result_width head argument_terms
          in SOME (call ("refute_word_asr " ^ Int.toString width)
            2 arguments) end
      | ("words", "word_lsb") => SOME (with_arity arguments 1 (fn values =>
          case values of [value] => "IntInf.mod (" ^ value ^ ", 2) = 1"
          | _ => raise Fail "word_lsb"))
      | ("words", "word_msb") =>
          let val width = word_result_width head argument_terms
          in SOME (with_arity arguments 1 (fn values =>
            case values of [value] => "refute_signed " ^
              Int.toString width ^ " " ^ atom value ^ " < 0"
            | _ => raise Fail "word_msb")) end
      | ("words", "word_lt") => SOME (compare true "<")
      | ("words", "word_le") => SOME (compare true "<=")
      | ("words", "word_gt") => SOME (compare true ">")
      | ("words", "word_ge") => SOME (compare true ">=")
      | ("words", "word_lo") => SOME (compare false "<")
      | ("words", "word_ls") => SOME (compare false "<=")
      | ("words", "word_hi") => SOME (compare false ">")
      | ("words", "word_hs") => SOME (compare false ">=")
      | ("words", "w2w") =>
          let val width = word_result_width head argument_terms
          in SOME (call ("refute_norm " ^ Int.toString width)
            1 arguments) end
      | ("words", "sw2sw") =>
          let
            val output_width = word_result_width head argument_terms
            val input_width = case argument_terms of
              argument :: _ => word_width (Term.type_of argument)
            | [] => output_width
          in
            SOME (with_arity arguments 1 (fn values =>
              case values of [value] => "refute_norm " ^
                Int.toString output_width ^ " (refute_signed " ^
                Int.toString input_width ^ " " ^ atom value ^ ")"
              | _ => raise Fail "sw2sw"))
          end
      | ("integer_word", "i2w") =>
          let val width = word_result_width head argument_terms
          in SOME (call ("refute_norm " ^ Int.toString width)
            1 arguments) end
      | ("integer_word", "w2i") =>
          let val width = case argument_terms of
                argument :: _ => word_width (Term.type_of argument)
              | [] => reject "w2i has no word argument"
          in SOME (call ("refute_signed " ^ Int.toString width)
            1 arguments) end
      | _ => record_primitive context head arguments
    end

  fun lazy_with_arity context arguments arity build =
    let
      val {delay, apply, ...} = context_operations context
      val supplied = Int.min (length arguments, arity)
      val initial = List.take (arguments, supplied)
      val extra = List.drop (arguments, supplied)
      val variables = List.tabulate (arity - supplied, fn index =>
        "refute_lazy_arg_" ^ Int.toString index)
      val body = build (initial @ variables)
      val abstraction = List.foldr (fn (variable, result) =>
        delay ("fn " ^ variable ^ " => " ^ result))
        body variables
    in
      List.foldl (fn (argument, result) =>
        apply result argument) abstraction extra
    end

  fun lazy_primitive context head argument_terms arguments =
    let
      val {delay, force, defer, apply, ...} =
        context_operations context
      val key = kname head
      val arity = length (#1 (boolSyntax.strip_fun (Term.type_of head)))
      fun unary operation = lazy_with_arity context arguments 1 (fn values =>
        case values of [value] => delay (operation (force value))
        | _ => raise Fail "lazy unary")
      fun binary operation = lazy_with_arity context arguments 2 (fn values =>
        case values of [left, right] =>
          delay (operation (force left, force right))
        | _ => raise Fail "lazy binary")
      fun flat () = lazy_with_arity context arguments arity (fn values =>
        let
          val forced = map force values
          val source = strict_primitive context head argument_terms forced
        in
          case source of
              SOME body => delay body
            | NONE => reject ("unsupported lazy primitive " ^
                              kname_text key)
        end)
      fun pair_selector index =
        lazy_with_arity context arguments 1 (fn values =>
        case values of
            [value] =>
              let
                val ty = #1 (Type.dom_rng (Term.type_of head))
                val _ = ignore (ensure_type context ty)
                val info = valOf (lookup_datatype context ty)
                val (_, _, constructor) = hd (#constructors info)
                val fields = if index = 0 then "left" else "right"
              in
                defer
                  (parens ("case " ^ force value ^ " of " ^ constructor ^
                    " (left, right) => " ^ fields))
              end
          | _ => raise Fail "lazy pair selector")
      fun list_info () =
        let
          val ty = #1 (Type.dom_rng (Term.type_of head))
          val _ = ignore (ensure_type context ty)
        in
          valOf (lookup_datatype context ty)
        end
      fun list_case value nil_body cons_body =
        let
          val info = list_info ()
          fun named name = valOf (List.find (fn (constructor, _, _) =>
            kname constructor = ("list", name)) (#constructors info))
          val (_, _, nil_name) = named "NIL"
          val (_, _, cons_name) = named "CONS"
        in
          "(case " ^ force value ^ " of " ^ nil_name ^ " => " ^ nil_body ^
          " | " ^ cons_name ^ " (refute_head, refute_tail) => " ^ cons_body ^
          ")"
        end
      fun lazy_list_nil () =
        let
          val info = list_info ()
        in
          #3 (valOf (List.find (fn (constructor, _, _) =>
            kname constructor = ("list", "NIL")) (#constructors info)))
        end
    in
      case key of
          ("bool", "T") => SOME (delay "true")
        | ("bool", "F") => SOME (delay "false")
        | ("bool", "ARB") => SOME
            (delay "(raise Refute_EvalSML.Stuck \"ARB\")")
        | ("bool", "~") => SOME
            (unary (fn value => "not " ^ parens value))
        | ("bool", "/\\") => SOME (binary (fn (left, right) =>
            left ^ " andalso " ^ right))
        | ("bool", "\\/") => SOME (binary (fn (left, right) =>
            left ^ " orelse " ^ right))
        | ("min", "==>") => SOME (binary (fn (left, right) =>
            "not " ^ parens left ^ " orelse " ^ right))
        | ("min", "=") =>
            let val compared = #1 (Type.dom_rng (Term.type_of head))
            in
              SOME (lazy_with_arity context arguments 2 (fn values =>
                case values of [left, right] =>
                  delay (equality_name context compared ^ " " ^
                    parens left ^ " " ^ parens right)
                | _ => raise Fail "lazy equality"))
            end
        | ("combin", "I") =>
            SOME (lazy_with_arity context arguments 1 (fn values =>
            case values of [value] => defer value
            | _ => raise Fail "lazy I"))
        | ("combin", "K") =>
            SOME (lazy_with_arity context arguments 2 (fn values =>
            case values of [value, _] => defer value
            | _ => raise Fail "lazy K"))
        | ("combin", "o") =>
            SOME (lazy_with_arity context arguments 3 (fn values =>
            case values of [f, g, x] => apply f (apply g x)
            | _ => raise Fail "lazy composition"))
        | ("pair", "FST") => SOME (pair_selector 0)
        | ("pair", "SND") => SOME (pair_selector 1)
        | ("list", "NULL") =>
            SOME (lazy_with_arity context arguments 1 (fn values =>
            case values of [value] => delay (list_case value "true" "false")
            | _ => raise Fail "lazy NULL"))
        | ("list", "HD") =>
            SOME (lazy_with_arity context arguments 1 (fn values =>
            case values of [value] => defer (list_case value
              "(raise Refute_EvalSML.Stuck \"HD []\")" "refute_head")
            | _ => raise Fail "lazy HD"))
        | ("list", "TL") =>
            SOME (lazy_with_arity context arguments 1 (fn values =>
            case values of [value] => defer (list_case value
              (delay (lazy_list_nil ())) "refute_tail")
            | _ => raise Fail "lazy TL"))
        | ("option", "THE") =>
            let
              fun build values =
                case values of
                    [value] =>
                      let
                        val ty = #1 (Type.dom_rng (Term.type_of head))
                        val _ = ignore (ensure_type context ty)
                        val info = valOf (lookup_datatype context ty)
                        fun named name = #3 (valOf (List.find
                          (fn (constructor, _, _) =>
                            kname constructor = ("option", name))
                          (#constructors info)))
                      in
                        defer
                          ("(case " ^ force value ^ " of " ^ named "NONE" ^
                           " => raise Refute_EvalSML.Stuck \"THE NONE\" | " ^
                           named "SOME" ^ " result => result)")
                      end
                  | _ => raise Fail "lazy THE"
            in SOME (lazy_with_arity context arguments 1 build) end
        | (thy, _) =>
            if Lib.mem thy
              ["num", "arithmetic", "prim_rec", "integer", "words",
               "integer_word"]
            then SOME (flat ())
            else NONE
    end

  fun primitive context head argument_terms arguments =
    choose (context_mode context)
      (fn () => strict_primitive context head argument_terms arguments)
      (fn () => lazy_primitive context head argument_terms arguments)

  datatype term_form =
      FVar | FCond | FLet | FNumeral | FIntLit | FChar | FString
    | FWord | FPair | FList | FPabs | FAbs | FOne | FRecord | FCase
    | FApp

  fun classify term =
    if Term.is_var term then FVar
    else if boolSyntax.is_cond term then FCond
    else if boolSyntax.is_let term then FLet
    else if Literal.is_numeral term then FNumeral
    else if intSyntax.is_int_literal term then FIntLit
    else if Literal.is_char_lit term then FChar
    else if Literal.is_string_lit term then FString
    else if wordsSyntax.is_word_literal term then FWord
    else if pairSyntax.is_pair term then FPair
    else if listSyntax.is_list term then FList
    else if pairSyntax.is_pabs term then FPabs
    else if Term.is_abs term then FAbs
    else if oneSyntax.is_one term then FOne
    else if TypeBase.is_record term then FRecord
    else if TypeBase.is_case term then FCase
    else FApp

  fun expression context term =
    case classify term of
        FLet => choose (context_mode context)
          (fn () => strict_let_expression context term)
          (fn () => lazy_let_expression context term)
      | FPabs => choose (context_mode context)
          (fn () => strict_pabs_expression context term)
          (fn () => lazy_pabs_expression context term)
      | FCase => choose (context_mode context)
          (fn () => strict_case_expression context term)
          (fn () => lazy_case_expression context term)
      | form => common_expression context form term

  and common_expression context form term =
    let
      val {delay, force, defer, apply, ...} =
        context_operations context

      fun named_constructor ty wanted =
        let
          val _ = ignore (ensure_type context ty)
          val info = valOf (lookup_datatype context ty)
        in
          #1 (valOf (List.find (fn (constructor, _, _) =>
            kname constructor = wanted) (#constructors info)))
        end

      fun list_value ty elements =
        let
          val nil_constructor = named_constructor ty ("list", "NIL")
          val cons_constructor = named_constructor ty ("list", "CONS")
          val empty = constructor_expression context nil_constructor []
        in
          List.foldr (fn (element, tail) =>
            constructor_expression context cons_constructor [element, tail])
            empty elements
        end

      fun strict_char_list_value ty elements =
        let
          val constructors = map (TypeBasePure.cinst ty)
            (TypeBase.constructors_of ty)
          fun named wanted =
            valOf (List.find (fn constructor =>
              kname constructor = wanted) constructors)
          val nil_constructor = named ("list", "NIL")
          val cons_constructor = named ("list", "CONS")
          val empty = constructor_expression context nil_constructor []
        in
          List.foldr (fn (element, tail) =>
            constructor_expression context cons_constructor [element, tail])
            empty elements
        end

      fun application head arguments =
        List.foldl (fn (argument, result) =>
          apply result argument) head arguments

      fun application_expression () =
        let
          val (head, argument_terms) = boolSyntax.strip_comb term
          val arguments = List.map (expression context) argument_terms
        in
          if Term.is_const head then
            (case primitive context head argument_terms arguments of
                 SOME result => result
               | NONE =>
                   if TypeBase.is_constructor head then
                     constructor_expression context head arguments
                   else
                     let
                       val name = ensure_definition context head
                       val (_, _, arity, _) =
                         valOf (lookup_definition context head)
                     in
                       choose (context_mode context)
                         (fn () =>
                           let
                             val base =
                               if arity = 0 then name ^ " ()" else name
                           in
                             List.foldl (fn (argument, result) =>
                               parens (result ^ " " ^ parens argument))
                               base arguments
                           end)
                         (fn () =>
                           let
                             fun invoke values = defer
                               (if null values then name ^ " ()"
                                else name ^ " " ^
                                  join " " (List.map parens values))
                           in
                             lazy_with_arity context arguments
                               arity invoke
                           end)
                     end)
          else
            choose (context_mode context)
              (fn () =>
                List.foldl (fn (argument, result) =>
                  parens (result ^ " " ^ parens argument))
                  (expression context head) arguments)
              (fn () =>
                application (expression context head) arguments)
        end
    in
      case form of
          FVar => variable_name term
        | FCond =>
            let val (condition, left, right) = boolSyntax.dest_cond term
            in
              choose (context_mode context)
                (fn () =>
                  parens ("if " ^ expression context condition ^ " then " ^
                    expression context left ^ " else " ^
                    expression context right))
                (fn () =>
                  defer
                    (parens ("if " ^ force (expression context condition) ^
                      " then " ^ expression context left ^ " else " ^
                      expression context right)))
            end
        | FNumeral =>
            choose (context_mode context)
              (fn () => num_literal (Literal.relaxed_dest_numeral term))
              (fn () =>
                delay (num_literal (Literal.relaxed_dest_numeral term)))
        | FIntLit =>
            choose (context_mode context)
              (fn () => int_literal (intSyntax.int_of_term term))
              (fn () => delay (int_literal (intSyntax.int_of_term term)))
        | FChar =>
            let
              val source =
                "#" ^ quote (String.str (Literal.dest_char_lit term))
            in
              choose (context_mode context)
                (fn () => source) (fn () => delay source)
            end
        | FString =>
            choose (context_mode context)
              (fn () => quote (Literal.relaxed_dest_string_lit term))
              (fn () =>
                let
                  val chars = List.map (fn character =>
                    delay ("#" ^ quote (String.str character)))
                    (String.explode
                      (Literal.relaxed_dest_string_lit term))
                in
                  list_value stringSyntax.string_ty chars
                end)
        | FWord =>
            choose (context_mode context)
              (fn () => num_literal (wordsSyntax.dest_word_literal term))
              (fn () =>
                delay (num_literal (wordsSyntax.dest_word_literal term)))
        | FPair =>
            let
              val (left, right) = pairSyntax.dest_pair term
            in
              choose (context_mode context)
                (fn () => parens (expression context left ^ ", " ^
                  expression context right))
                (fn () =>
                  let
                    val ty = Term.type_of term
                    val constructor = TypeBasePure.cinst ty
                      (hd (TypeBase.constructors_of ty))
                  in
                    constructor_expression context constructor
                      [expression context left, expression context right]
                  end)
            end
        | FList =>
            let
              val (elements, _) = listSyntax.dest_list term
              val compiled = List.map (expression context) elements
            in
              choose (context_mode context)
                (fn () =>
                  if is_char_list (Term.type_of term) then
                    strict_char_list_value (Term.type_of term) compiled
                  else "[" ^ join ", " compiled ^ "]")
                (fn () => list_value (Term.type_of term) compiled)
            end
        | FAbs =>
            let val (argument, body) = Term.dest_abs term
            in
              choose (context_mode context)
                (fn () => parens ("fn " ^ variable_name argument ^ " => " ^
                  expression context body))
                (fn () => delay ("fn " ^ variable_name argument ^ " => " ^
                  expression context body))
            end
        | FOne => choose (context_mode context)
            (fn () => "()") (fn () => delay "()")
        | FRecord =>
            let
              val (record_ty, fields) = TypeBase.dest_record term
              val constructor = hd (TypeBase.constructors_of record_ty)
            in
              constructor_expression context constructor
                (List.map (expression context o #2) fields)
            end
        | FApp => application_expression ()
        | FLet => raise Fail "common let expression"
        | FPabs => raise Fail "common paired abstraction"
        | FCase => raise Fail "common case expression"
    end

  and strict_let_expression context term =
    let
      val (groups, body) = pairSyntax.strip_anylet term
      fun binding (left, right) =
        pattern context left ^ " = " ^ expression context right
      (* A binding group from [strip_anylet] is simultaneous.  SML's
         [val ... and ...] preserves that scope, whereas separate [val]
         declarations would let later right-hand sides capture earlier
         bindings. *)
      fun group [] = ""
        | group (first :: rest) =
            "val " ^ binding first ^ join "\nand " (List.map binding rest)
    in
      parens ("let\n" ^ join "\n" (List.map group groups) ^ "\nin " ^
        expression context body ^ "\nend")
    end

  and lazy_let_expression context term =
    let
      val {defer, ...} = context_operations context
      val (groups, body) = pairSyntax.strip_anylet term
      fun compile_groups [] = expression context body
        | compile_groups (bindings :: rest) =
            let
              val values = List.map (fn _ =>
                fresh_pattern context "refute_lazy_let_") bindings
              val declarations = ListPair.map
                (fn ((_, right), value) =>
                  "val " ^ value ^ " = " ^ expression context right)
                (bindings, values)
              val matched = List.foldr
                (fn (((left, _), value), success) =>
                  lazy_match_pattern context left value success
                    "(raise Match)")
                (compile_groups rest)
                (ListPair.zip (bindings, values))
            in
              parens ("let\n" ^ join "\n" declarations ^ "\nin " ^
                matched ^ "\nend")
            end
    in
      defer (compile_groups groups)
    end

  and strict_pabs_expression context term =
    let val (argument, body) = pairSyntax.dest_pabs term
    in
      parens ("fn " ^ pattern context argument ^ " => " ^
        expression context body)
    end

  and lazy_pabs_expression context term =
    let
      val {delay, ...} = context_operations context
      val (argument, body) = pairSyntax.dest_pabs term
      val argument_name = fresh_pattern context
        "refute_lazy_pair_argument_"
      val matched = lazy_match_pattern context argument argument_name
        (expression context body) "(raise Match)"
    in
      delay ("fn " ^ argument_name ^ " => " ^ matched)
    end

  and strict_case_expression context term =
    let
      val (scrutinee, rows) = TypeBase.strip_case term
      fun row (pat, rhs) = pattern context pat ^ " => " ^
        expression context rhs
      (* Strings are represented as ML strings, not ML lists.  Compile their
         rows through the observation matcher so literal and nested patterns
         preserve source order without emitting string expressions as SML
         patterns. *)
      fun string_rows () =
        let
          val value = fresh_pattern context "refute_string_scrutinee_"
          fun dispatch [] = "(raise Match)"
            | dispatch ((pat, rhs) :: rest) =
                let val next = fresh_pattern context "refute_string_next_"
                in
                  "let fun " ^ next ^ " () = " ^ dispatch rest ^ " in " ^
                  lazy_match_pattern context pat value
                    (expression context rhs) (next ^ " ()") ^ " end"
                end
        in
          parens ("let val " ^ value ^ " = " ^ expression context scrutinee ^
            " in " ^ dispatch rows ^ " end")
        end
    in
      if is_char_list (Term.type_of scrutinee) then string_rows ()
      else parens ("case " ^ expression context scrutinee ^ " of " ^
        join " | " (List.map row rows))
    end

  and lazy_case_expression context term =
    let
      val {defer, ...} = context_operations context
      val (scrutinee, rows) = TypeBase.strip_case term
      val value = fresh_pattern context "refute_lazy_scrutinee_"
      fun dispatch [] = "(raise Match)"
        | dispatch ((pat, rhs) :: rest) =
            let
              val next = fresh_pattern context "refute_lazy_next_"
              val failure = next ^ " ()"
            in
              parens ("let fun " ^ next ^ " () = " ^ dispatch rest ^
                " in " ^ lazy_match_pattern context pat value
                  (expression context rhs) failure ^ " end")
            end
    in
      defer
        (parens ("let val " ^ value ^ " = " ^
          expression context scrutinee ^ "\nin " ^ dispatch rows ^
          "\nend"))
    end

  (* Match one HOL pattern against a suspended value.  Constructor spines and
     literals are observations, so they force the suspension being tested.
     Constructor fields remain suspended: variable and wildcard fields are
     bound or skipped as-is, while nested tests observe fields left-to-right.
     Keeping failure explicit also lets case rows and definition clauses share
     this compiler without relying on eager SML patterns. *)
  and lazy_match_pattern context tm value success failure =
    lazy_match_pattern_with context [] tm value success failure

  and lazy_match_pattern_with context initial_bound tm value success failure =
    let
      val {delay, force, ...} = context_operations context
      fun variables pattern = Term.free_vars_lr pattern
      fun match bound pattern matched success =
        if Term.is_var pattern then
          let val variable = variable_name pattern
          in
            if variable = "_" then success
            else
              case List.find (fn previous =>
                     Term.aconv previous pattern) bound of
                  SOME previous =>
                    "if " ^ equality_name context (Term.type_of pattern) ^
                    " " ^ parens matched ^ " " ^
                    parens (variable_name previous) ^ " then " ^
                    success ^ " else " ^ failure
                | NONE => "let val " ^ variable ^ " = " ^ matched ^ " in " ^
                    success ^ " end"
          end
        else if Literal.is_numeral pattern orelse
                intSyntax.is_int_literal pattern orelse
                Literal.is_char_lit pattern orelse
                Literal.is_string_lit pattern orelse oneSyntax.is_one pattern
                orelse Term.aconv pattern boolSyntax.T orelse
                Term.aconv pattern boolSyntax.F orelse
                wordsSyntax.is_word_literal pattern then
          "if " ^ equality_name context (Term.type_of pattern) ^ " " ^
            parens matched ^ " " ^ parens (expression context pattern) ^
            " then " ^ success ^ " else " ^ failure
        else
          let
            val (head, arguments) = boolSyntax.strip_comb pattern
            (* A char list is an ML string in strict mode only:
               [classify_primitive] offers [MLString] through [algebraic],
               which is [NONE] in lazy mode, so a lazy char list is a
               suspension of a generated list datatype and its constructors
               have to be observed as such.  The type alone does not say
               which, and testing it alone emitted [String.size] against a
               datatype value -- generated SML that does not typecheck. *)
            val char_list = is_char_list (Term.type_of pattern) andalso
              choose (context_mode context) (fn () => true) (fn () => false)
            fun match_children bound [] [] = success
              | match_children bound (argument :: arguments)
                  (child :: children) =
                  match bound argument child
                    (match_children (bound @ variables argument) arguments
                       children)
              | match_children _ _ _ = raise Fail "malformed constructor"
          in
            if Term.is_const head andalso
               kname head = ("list", "NIL") andalso char_list then
              "if String.size " ^ parens (force matched) ^ " = 0 then " ^
                success ^ " else " ^ failure
            else if Term.is_const head andalso
                    kname head = ("list", "CONS") andalso char_list then
              (case arguments of
                   [first, rest] =>
                     let
                       val text = fresh_pattern context "refute_lazy_string_"
                       val head_value = delay
                         ("String.sub " ^ parens (text ^ ", 0"))
                       val tail_value = delay
                         ("String.extract " ^ parens (text ^ ", 1, NONE"))
                       val body = match bound first head_value
                         (match (bound @ variables first) rest tail_value
                            success)
                     in
                       "let val " ^ text ^ " = " ^ force matched ^
                       " in if String.size " ^ text ^ " > 0 then " ^ body ^
                       " else " ^ failure ^ " end"
                     end
                 | _ => reject "malformed string CONS pattern")
            else if Term.is_const head andalso
                    kname head = ("num", "SUC") then
              (case arguments of
                   [argument] =>
                     let
                       val raw = fresh_pattern context "refute_lazy_suc_"
                       val predecessor = delay (parens (raw ^ " - 1"))
                     in
                       "let val " ^ raw ^ " = " ^ force matched ^ " in " ^
                       "if " ^ raw ^ " > 0 then " ^
                       match bound argument predecessor success ^
                       " else " ^ failure ^ " end"
                     end
                 | _ => reject "malformed lazy SUC pattern")
            else if Term.is_const head andalso TypeBase.is_constructor head then
              let
                val children = List.map (fn _ =>
                  fresh_pattern context "refute_lazy_field_") arguments
                (* Strict extraction keeps lists, options and pairs in their
                   native SML representations, so those constructors have no
                   generated datatype to look up.  Observe them through the
                   patterns the strict expression compiler emits; only the
                   lazy representation makes every type a datatype. *)
                fun native () =
                  case (kname head, children) of
                      (("list", "NIL"), []) => SOME "[]"
                    | (("list", "CONS"), [first, rest]) =>
                        SOME (parens (first ^ " :: " ^ rest))
                    | (("option", "NONE"), []) => SOME "NONE"
                    | (("option", "SOME"), [child]) => SOME ("SOME " ^ child)
                    | (("pair", ","), [left, right]) =>
                        SOME (parens (left ^ ", " ^ right))
                    | _ => NONE
                fun generated () =
                  case constructor_for context head of
                      SOME (_, _, constructor) =>
                        (case children of
                             [] => constructor
                           | [child] => constructor ^ " " ^ child
                           | fields => constructor ^ " (" ^
                               join ", " fields ^ ")")
                    | NONE => reject ("unknown pattern constructor " ^
                                      kname_text (kname head))
                val payload =
                  case choose (context_mode context) native (fn () => NONE) of
                      SOME text => text
                    | NONE => generated ()
                val body = match_children bound arguments children
              in
                parens ("case " ^ force matched ^ " of " ^
                  payload ^ " => " ^ body ^ " | _ => " ^ failure)
              end
            else
              (* This matcher serves strict extraction too, so its refusals
                 must not blame lazy mode: [definition_clause] routes every
                 clause here, and the strict expression compiler's own
                 [pattern] refuses the same shape in the same words. *)
              reject ("non-constructor pattern: " ^
                      Parse.term_to_string pattern)
          end
    in
      match initial_bound tm value success
    end

  fun lazy_definition_clause context (constant, name, arity, theorem) =
    let
      val equations = definition_equations constant theorem
      val _ = if length (#1 (hd equations)) = arity then ()
        else raise Fail "cached definition arity changed"
      val arguments = List.tabulate (arity, fn index =>
        "refute_argument_" ^ Int.toString index)
      fun dispatch [] = "(raise Match)"
        | dispatch ((patterns, rhs) :: rest) =
            let
              val fallback = "refute_next ()"
              fun match_arguments bound [] [] = expression context rhs
                | match_arguments bound (pattern :: patterns)
                    (argument :: arguments) =
                    lazy_match_pattern_with context bound pattern argument
                      (match_arguments
                         (bound @ Term.free_vars_lr pattern)
                         patterns arguments)
                      fallback
                | match_arguments _ _ _ = raise Fail "malformed rule"
              val body = match_arguments [] patterns arguments
            in
              "(let fun refute_next () = " ^ dispatch rest ^ " in " ^
              body ^ " end)"
            end
      val lhs = if null arguments then name ^ " ()"
                else name ^ " " ^ join " " arguments
    in
      lhs ^ " = " ^ dispatch equations
    end

  fun definition_clause context item =
    (* The observation matcher also serves strict extraction: its strict
       operations are identities.  In particular this avoids rendering a
       char-list CONS expression as an SML pattern in definition clauses. *)
    lazy_definition_clause context item

  (* Compiling a clause is the expensive part of extraction and its text
     is final once produced (names are fixed at registration), so the
     drain pass and the declarations pass share one compilation. *)
  fun cached_definition_clause context (item as (constant, _, _, _)) =
    case List.find (fn (other, _) => same_term other constant)
      (!(#definition_clauses context)) of
      SOME (_, clause) => clause
    | NONE =>
        let
          val clause = definition_clause context item
          val _ = #definition_clauses context :=
            (constant, clause) :: !(#definition_clauses context)
        in
          clause
        end

  (* Compiling a clause can register further definitions, so each round
     picks up whatever was prepended since the last one.  Counting the
     entries already drained keeps that cheap: the list is append-only and
     carries no duplicates, so the new items are exactly its fresh prefix,
     and no term comparison is needed to recognize them. *)
  fun drain_definitions context =
    let
      fun loop drained =
        let
          val current = !(#definitions context)
          val available = length current
        in
          if available <= drained then ()
          else
            let
              val fresh = rev (List.take (current, available - drained))
            in
              List.app (ignore o cached_definition_clause context) fresh;
              loop available
            end
        end
    in
      loop 0
    end

  fun definition_declarations context =
    let
      val definitions = rev (!(#definitions context))
      val groups = rev (!(#definition_groups context))
      fun item_for constant =
        case List.find (fn (other, _, _, _) => same_term other constant)
          definitions of
          SOME item => item
        | NONE => raise Fail "Refute_Extract: missing definition"
      fun group_for constant =
        List.find (List.exists (same_term constant)) groups
      fun constants_in (_, _, _, theorem) =
        HolKernel.find_terms Term.is_const (Thm.concl theorem)
      fun same_group left right =
        List.all (fn constant => List.exists (same_term constant) right)
          left andalso
        List.all (fn constant => List.exists (same_term constant) left)
          right
      fun add_group group groups =
        if List.exists (same_group group) groups then groups
        else group :: groups
      fun dependencies group =
        let
          fun add (dependency, result) =
            if List.exists (same_term dependency) group then result
            else
              case group_for dependency of
                NONE => result
              | SOME found => add_group found result
        in
          List.foldl add []
            (List.concat (List.map (constants_in o item_for) group))
        end
      fun group_done emitted group =
        List.exists (fn done =>
          List.all (fn constant => List.exists (same_term constant) done)
            group) emitted
      fun ready emitted (_, deps) =
        List.all (group_done emitted) deps
      fun order emitted [] = rev emitted
        | order emitted remaining =
            (case List.partition (ready emitted) remaining of
               ([], _) =>
                 reject "definition dependency cycle outside a mutual group"
             | (now, later) =>
                 order (rev (List.map #1 now) @ emitted) later)
      fun one keyword item =
        keyword ^ " " ^ cached_definition_clause context item
      fun declaration group =
        case List.map item_for group of
          [] => ""
        | first :: rest =>
            join "\n" (one "fun" first :: List.map (one "and") rest)
      val ordered =
        order [] (List.map (fn group => (group, dependencies group)) groups)
    in
      case groups of
        [] => ""
      | _ => join "\n" (List.map declaration ordered) ^ "\n"
    end

  fun source_prefix context =
    prelude ^ "\n" ^
    choose (context_mode context)
      (fn () => "")
      (fn () =>
        "fun refute_hole position = Refute_EvalSML.lazy_hole position\n\n") ^
    String.concat (List.map (datatype_declaration context)
      (datatype_groups context)) ^ "\n" ^
    equality_declarations context ^ "\n"

  fun compile_types_with mode types =
    let
      val context = new_context mode
      val mltypes = List.map (ensure_type context) types
      (* This utility describes representation types only.  Requesting
         equality here can make a perfectly extractable function type fail:
         structural function equality would need to enumerate its domain. *)
      val source = source_prefix context
      val ml_type =
        case mltypes of
          [mlty] => ml_ty_text mlty
        | _ => ml_ty_text (MLTuple mltypes)
    in
      {source = source, ml_type = ml_type}
    end

  fun compile_types types = compile_types_with Strict types
  fun compile_type ty = compile_types [ty]

  fun extract_term_with mode term =
    let
      val context = new_context mode
      val _ = ignore (ensure_type context (Term.type_of term))
      val entry_expression = expression context term
      val _ = drain_definitions context
      val source = source_prefix context ^
        definition_declarations context ^ "\nfun entry () = " ^
        entry_expression ^ "\n"
    in
      {source = source, entry = "entry ()"}
    end

  fun extract_term term = extract_term_with Strict term
  fun extract_lazy_term term = extract_term_with Lazy term

  fun extract_tests_with mode
        (config : Refute_Core.config) strategy plans : registered_extraction =
    let
      open Refute_Eval

      (* One immutable cache view governs validation, dependency closure and
         emission for this compile call. *)
      val enum_cache = Refute_SmartGen.enumerator_snapshot ()
      val context = new_context mode
      val constructor_terms =
        {list = ref ([] : term list), count = ref 0,
         indexes = ref (Redblackmap.mkDict Term.compare)}
      val raw_terms =
        {list = ref ([] : term list), count = ref 0,
         indexes = ref (Redblackmap.mkDict Term.compare)}
      val next_bound = ref 0
      val original_variables = ref ([] : (term * term) list)

      fun fresh_bound original =
        let
          val serial = !next_bound
          val _ = next_bound := serial + 1
          val safe = Term.mk_var
            ("refute_bound_" ^ Int.toString serial, Term.type_of original)
          val _ = original_variables :=
            (safe, original) :: !original_variables
        in
          safe
        end

      fun original_variable safe =
        case List.find (fn (renamed, _) => Term.aconv renamed safe)
          (!original_variables) of
          SOME (_, original) => original
        | NONE => safe

      fun substitute_variables environment tm =
        Term.subst (List.map (fn (original, renamed) =>
          {redex = original, residue = renamed}) environment) tm

      fun rename_plan current environment =
        case current of
          Test tm => Test (substitute_variables environment tm)
        | Gen (variable, next) =>
            let val safe = fresh_bound variable
            in Gen (safe, rename_plan next ((variable, safe) :: environment))
            end
        | Bind (variable, tm, fallback, next) =>
            let
              val safe = fresh_bound variable
              val renamed_tm = substitute_variables environment tm
              val renamed_fallback =
                Option.map (fn other => rename_plan other environment) fallback
              val renamed_next = rename_plan next
                ((variable, safe) :: environment)
            in
              Bind (safe, renamed_tm, renamed_fallback, renamed_next)
            end
        | Split (tm, branches) =>
            let
              fun branch (constructor, variables, next) =
                let
                  val safe = List.map fresh_bound variables
                  val additions = ListPair.zip (variables, safe)
                in
                  (constructor, safe,
                   rename_plan next (additions @ environment))
                end
            in
              Split (substitute_variables environment tm,
                List.map branch branches)
            end
        | Guard (tm, next) =>
            Guard (substitute_variables environment tm,
              rename_plan next environment)
        | NegGuard (tm, next) =>
            NegGuard (substitute_variables environment tm,
              rename_plan next environment)
        | SmartGuard {predicate, version, cont} =>
            SmartGuard
              {predicate = substitute_variables environment predicate,
               version = version, cont = rename_plan cont environment}
        | Enum {rel, mode, version, ins, outs, cont} =>
            let
              val bound = map #1 environment
              val output_variables = List.foldl (fn (variable, result) =>
                if Util.aconv_member variable (bound @ result)
                then result else result @ [variable]) []
                (List.concat (map Term.free_vars_lr outs))
              val safe = map fresh_bound output_variables
              val additions = ListPair.zip (output_variables, safe)
              val extended = additions @ environment
            in
              Enum {rel = rel, mode = mode, version = version,
                    ins = map (substitute_variables environment) ins,
                    outs = map (substitute_variables extended) outs,
                    cont = rename_plan cont extended}
            end
        | Prune => Prune

      val plans = List.map (fn plan => rename_plan plan []) plans

      (* Lazy extraction installs only the property compiler.  Generation
         and refinement belong to the narrowing engine; accepting those nodes
         here would accidentally run strict enumeration over lazy values.
         No plan reaches this today: [Refute_EvalSML.compile_locked] picks
         [Lazy] only for [Narrowing], and the one [Narrowing] compile call
         ([Refute_QC_Narrow.compile_instances_window]) supplies a [Pnf]
         problem or raises, so [extract_tests_with] never runs under
         [Lazy].  The guard stays complete for every node regardless. *)
      fun test_only current =
        case current of
            Test _ => true
          | Guard (_, next) => test_only next
          | NegGuard (_, next) => test_only next
          | Prune => true
          | _ => false
      val _ =
        if mode = Lazy andalso not (List.all test_only plans) then
          reject "native: narrowing engine is not installed"
        else ()

      fun smart_reject message = reject ("smart plan: " ^ message)

      val same_program = Refute_EvalEnum.same_program

      fun cached_all_input predicate expected_version =
        if not (#smart_generators (#qc config)) orelse
           strategy <> Exhaustive then NONE
        else
          let
            val (head, arguments) = HolKernel.strip_comb predicate
            fun find {program =
                  (program as {relation, mode, version, ...} :
                    Refute_SmartGen.enumerator), ...} =
              if Refute_SmartGen.same_relation
                   (Refute_SmartGen.Predicate head) relation andalso
                 Refute_SmartGen.same_program_version
                   (expected_version, version) andalso
                 Refute_SmartGen.program_is_fresh program andalso
                 Theory.uptodate_term predicate
              then
                case Refute_SmartGen.top_level_parts mode arguments of
                    SOME (ins, []) => SOME (program, ins)
                  | _ => NONE
              else NONE
          in
            Lib.get_first find enum_cache
          end
        handle Feedback.HOL_ERR _ => NONE

      fun enum_dependency rel mode =
        Refute_SmartGen.enumerator_for_in enum_cache rel mode

      fun top_program rel mode version =
        case enum_dependency rel mode of
            SOME found =>
              if Refute_SmartGen.same_program_version
                   (version, #version found)
              then found
              else smart_reject "stale Enum version"
          | NONE => smart_reject "missing top-level enumerator program"

      fun guard_program predicate version =
        case cached_all_input predicate version of
            SOME (found, _) => found
          | NONE => smart_reject "stale or non-all-input smart Guard"

      val collect_programs = Refute_EvalEnum.collect_programs
        smart_reject enum_dependency top_program guard_program

      val enum_programs = List.foldl (fn (plan, programs) =>
        collect_programs plan programs) [] plans

      val _ = Refute_EvalEnum.validate
        smart_reject enum_programs plans

      (* Enumerator clauses come from arbitrary HOL source.  Rename every
         clause-local variable into a generated namespace whose sanitized
         spelling is injective and disjoint from all emitter helper names. *)
      val next_enum_local = ref 0
      fun fresh_enum_local variable =
        let val serial = !next_enum_local
            val _ = next_enum_local := serial + 1
        in
          Term.mk_var ("refute_enum_local_" ^ Int.toString serial,
            Term.type_of variable)
        end
      fun rename_program
            ({relation, mode, version, clauses} :
              Refute_SmartGen.enumerator) =
        let
          fun rename_clause (Refute_SmartGen.CpsClause
                {ins, premises, outs}) =
            let
              fun premise_terms premise =
                case premise of
                    Refute_SmartGen.CpsCall {ins, outs, ...} => ins @ outs
                  | Refute_SmartGen.CpsGuard tm => [tm]
                  | Refute_SmartGen.CpsGenerate variable => [variable]
              val terms = ins @ List.concat (map premise_terms premises) @ outs
              val variables = List.foldl (fn (variable, result) =>
                if Util.aconv_member variable result
                then result else result @ [variable]) []
                (List.concat (map Term.free_vars_lr terms))
              val renamed = map fresh_enum_local variables
              val substitution = ListPair.mapEq (fn (old, fresh) =>
                {redex = old, residue = fresh}) (variables, renamed)
              fun sub tm = Term.subst substitution tm
              fun sub_premise premise =
                case premise of
                    Refute_SmartGen.CpsCall {rel, mode, ins, outs} =>
                      Refute_SmartGen.CpsCall
                        {rel = rel, mode = mode, ins = map sub ins,
                         outs = map sub outs}
                  | Refute_SmartGen.CpsGuard tm =>
                      Refute_SmartGen.CpsGuard (sub tm)
                  | Refute_SmartGen.CpsGenerate variable =>
                      Refute_SmartGen.CpsGenerate (sub variable)
            in
              Refute_SmartGen.CpsClause
                {ins = map sub ins, premises = map sub_premise premises,
                 outs = map sub outs}
            end
        in
          {relation = relation, mode = mode, version = version,
           clauses = map rename_clause clauses}
        end
      val enum_programs = map rename_program enum_programs

      fun index_term {list, count, indexes} tm =
        case Redblackmap.peek (!indexes, tm) of
          SOME index => index
        | NONE =>
            let val index = !count
                val _ = indexes := Redblackmap.insert (!indexes, tm, index)
                val _ = list := tm :: !list
                val _ = count := index + 1
            in index end

      fun constructor_index tm = index_term constructor_terms tm
      fun raw_index tm = index_term raw_terms tm
      fun intinf value =
        "(valOf (IntInf.fromString " ^ quote (IntInf.toString value) ^ ") " ^
        ": IntInf.int)"
      fun pair value thunk = parens (value ^ ", " ^ thunk)
      fun thunk body = "(fn () => " ^ body ^ ")"
      fun term_list items = "[" ^ join ", " items ^ "]"
      fun maximum values = List.foldl Int.max 0 values

      fun custom_type ty = Refute_Gen.has_registered_generator ty

      val validated = ref ([] : hol_type list)

      fun validate_type root ty =
        if Util.member_type ty (!validated) then ()
        else
          let
            val _ = validated := ty :: !validated
            val _ =
              if custom_type ty then
                reject ("custom generator registered for " ^ type_name root)
              else ()
          in
            case Refute_Gen.spec_of ty of
              Refute_Gen.GenDatatype {constrs, family, ...} =>
                ((case strategy of
                    Exhaustive =>
                      if Refute_Gen.datatype_recursive_under_function
                        family constrs
                      then
                        reject ("Creation of exhaustive generators failed " ^
                          "because the datatype is recursive under a " ^
                          "function type: " ^ type_name ty)
                      else ()
                  | Random _ => ()
                  | Narrowing => ());
                 List.app (validate_type root)
                   (List.concat (List.map #2 constrs)))
            | Refute_Gen.GenFun (domain, range) =>
                (validate_type root domain; validate_type root range)
            | Refute_Gen.GenCustom _ =>
                reject ("custom generator registered for " ^ type_name root)
            | Refute_Gen.GenNum (Refute_Gen.Word width) =>
                (case strategy of
                   Random _ =>
                     if width <= 32 then ()
                     else reject ("word width exceeds rand_below's " ^
                       "32-bit bound for " ^ type_name root)
                 | Exhaustive => ()
                 | Narrowing => ())
            | _ => ()
          end
          handle Refute_Gen.NoGenerator (missing, why) =>
            reject ("no generator for " ^ type_name missing ^ " — " ^ why)

      val root_types = Lib.mk_set
        (List.concat (List.map plan_gen_types plans) @
         List.concat (map Refute_SmartGen.enumerator_gen_types enum_programs))
      val _ = List.app (fn ty => validate_type ty ty) root_types

      fun dependencies ty =
        case Refute_Gen.spec_of ty of
          Refute_Gen.GenDatatype {constrs, ...} =>
            List.concat (List.map #2 constrs)
        | Refute_Gen.GenFun (domain, range) => [domain, range]
        | _ => []

      fun close_types [] seen = rev seen
        | close_types (ty :: rest) seen =
            if Util.member_type ty seen then close_types rest seen
            else close_types (dependencies ty @ rest) (ty :: seen)

      val generator_types = close_types root_types []
      val _ = List.app (fn ty => ignore (ensure_type context ty))
        generator_types

      fun generator_name prefix ty =
        let
          val index = Lib.index (Util.same_type ty) generator_types
        in prefix ^ Int.toString index end

      fun raw_reconstruction tm =
        thunk ("Refute_EvalSML.raw_term " ^ integer (raw_index tm))

      fun reconstruction tm =
        if Literal.is_numeral tm then
          thunk ("Refute_EvalSML.num_term " ^
            num_literal (Literal.relaxed_dest_numeral tm))
        else if intSyntax.is_int_literal tm then
          thunk ("Refute_EvalSML.int_term " ^
            int_literal (intSyntax.int_of_term tm))
        else if Literal.is_char_lit tm then
          thunk ("Refute_EvalSML.char_term #" ^
            quote (String.str (Literal.dest_char_lit tm)))
        else if Literal.is_string_lit tm then
          thunk ("Refute_EvalSML.string_term " ^
            quote (Literal.relaxed_dest_string_lit tm))
        else if wordsSyntax.is_word_literal tm then
          thunk ("Refute_EvalSML.word_term " ^
            integer (word_width (Term.type_of tm)) ^ " " ^
            num_literal (wordsSyntax.dest_word_literal tm))
        else
          let val (head, arguments) = boolSyntax.strip_comb tm
          in
            if Term.is_const head andalso TypeBase.is_constructor head then
              let
                val index = constructor_index head
                val children = List.map reconstruction arguments
                val forced = List.map (fn child => parens child ^ " ()")
                  children
              in
                thunk ("Refute_EvalSML.con_term " ^ integer index ^ " " ^
                  term_list forced)
              end
            else raw_reconstruction tm
          end

      fun generated_value tm =
        pair (expression context tm) (reconstruction tm)

      fun enum_source ty =
        case Refute_Gen.enumerate ty of
          SOME values => term_list (List.map generated_value values)
        | NONE => raise Fail "Refute_Extract: enum_source"

      val generator_runtime =
        "datatype refute_attempt =\n" ^
        "    RefuteContinue\n" ^
        "  | RefuteGuardSuccess\n" ^
        "  | RefuteHit of Refute_EvalSML.generated_hit\n" ^
        "fun refute_hit found =\n" ^
        "  if (!Refute_EvalSML.ignored_filter) found then\n" ^
        "    RefuteContinue\n" ^
        "  else RefuteHit found\n" ^
        "fun refute_each [] continuation = RefuteContinue\n" ^
        "  | refute_each (value :: values) continuation =\n" ^
        "      (case continuation value of\n" ^
        "         RefuteContinue => refute_each values continuation\n" ^
        "       | answer => answer)\n" ^
        "fun refute_range first last make =\n" ^
        "  if first > last then []\n" ^
        "  else make first :: refute_range (first + 1) last make\n" ^
        "fun refute_rand_below bound state =\n" ^
        "  if bound <= 0 orelse bound > 4294967296 then\n" ^
        "    raise Fail \"Refute generated rand_below bound\"\n" ^
        "  else Refute_Eval.rand_below bound state\n"

      fun constructor_value constructor values =
        constructor_expression context constructor (List.map #1 values)

      fun constructor_thunk constructor values =
        let
          val index = constructor_index constructor
          val forced = List.map (fn (_, term) => parens term ^ " ()") values
        in
          thunk ("Refute_EvalSML.con_term " ^ integer index ^ " " ^
            term_list forced)
        end

      fun exhaustive_num kind =
        case kind of
          Refute_Gen.Num =>
            "refute_range 0 (Int.max (0, size)) (fn n => " ^
            pair ("IntInf.fromInt n")
              (thunk "Refute_EvalSML.num_term (IntInf.fromInt n)") ^ ")"
        | Refute_Gen.Int =>
            "refute_range (~(Int.max (0, size))) (Int.max (0, size)) " ^
            "(fn n => " ^ pair ("IntInf.fromInt n")
              (thunk "Refute_EvalSML.int_term (IntInf.fromInt n)") ^ ")"
        | Refute_Gen.Char =>
            "refute_range 0 255 (fn n => " ^
            pair ("Char.chr n")
              (thunk "Refute_EvalSML.char_term (Char.chr n)") ^ ")"
        | Refute_Gen.Word width =>
            "refute_range 0 " ^
            (if width <= 8 then
               "(IntInf.toInt (IntInf.pow (2, " ^ integer width ^
               ") - 1))"
             else
               "(IntInf.toInt (IntInf.min " ^
               "(IntInf.fromInt (Int.max (0, size)), " ^
               "IntInf.pow (2, " ^ integer width ^ ") - 1)))") ^
            " (fn n => " ^ pair ("IntInf.fromInt n")
              (thunk ("Refute_EvalSML.word_term " ^ integer width ^
                " (IntInf.fromInt n)")) ^ ")"

      fun exhaustive_arguments [] _ continuation = continuation []
        | exhaustive_arguments (ty :: tys) size continuation =
            let
              val value = "refute_value_" ^ integer (length tys)
              val term = "refute_term_" ^ integer (length tys)
              val call = generator_name "exh_" ty
            in
              call ^ " (fn (" ^ value ^ ", " ^ term ^ ") => " ^
              exhaustive_arguments tys size (fn values =>
                continuation ((value, term) :: values)) ^ ") " ^ size ^
              " complete"
            end

      fun exhaustive_constructor (constructor, argument_types) =
        exhaustive_arguments argument_types "(size - 1)" (fn reversed =>
          let
            val values = reversed
          in
            "continuation " ^ pair
              (constructor_value constructor values)
              (constructor_thunk constructor values)
          end)

      fun exhaustive_datatype constrs =
        let
          fun choices [] = "RefuteContinue"
            | choices (constructor :: rest) =
                "(case " ^ exhaustive_constructor constructor ^ " of " ^
                "RefuteContinue => " ^ choices rest ^ " | answer => answer)"
        in
          "if size <= 0 then RefuteContinue else " ^ choices constrs
        end

      fun exhaustive_function domain range =
        let
          val domain_gen = generator_name "exh_" domain
          val range_gen = generator_name "exh_" range
          val equality = equality_name context domain
          (* The reconstructed witness is displayed as a lambda, so this
             name is user-facing; [Refute_EvalSML.fun_term] keeps it clear
             of the body it ends up binding. *)
          val variable = Term.mk_var ("x", domain)
          val variable_index = raw_index variable
          val update_value =
            pair
              (parens ("fn x => if " ^ equality ^ " x point then value " ^
                "else base x"))
              (thunk ("Refute_EvalSML.update_term (point_term ()) " ^
                "(value_term ()) (base_term ())"))
        in
          "let\n" ^
          "  fun constants () =\n" ^
          "    " ^ range_gen ^ " (fn (default, default_term) =>\n" ^
          "      continuation " ^ pair
            (parens "fn _ => default")
            (thunk ("Refute_EvalSML.fun_term " ^
              "(Refute_EvalSML.raw_term " ^ integer variable_index ^ ") " ^
              "(default_term ()) []")) ^ ") size complete\n" ^
          "  fun layers 0 = RefuteContinue\n" ^
          "    | layers remaining =\n" ^
          "      " ^ domain_gen ^ " (fn (point, point_term) =>\n" ^
          "        " ^ range_gen ^ " (fn (value, value_term) =>\n" ^
          "          " ^ generator_name "exh_"
            (Type.mk_type ("fun", [domain, range])) ^
          " (fn (base, base_term) => continuation " ^ update_value ^ ") " ^
          "(remaining - 1) complete) size complete) size complete\n" ^
          "in case constants () of\n" ^
          "     RefuteContinue => layers size\n" ^
          "   | answer => answer\n" ^
          "end"
        end

      fun exhaustive_body ty =
        case Refute_Gen.spec_of ty of
          Refute_Gen.GenEnum _ =>
            "refute_each " ^ enum_source ty ^ " continuation"
        | Refute_Gen.GenNum kind =>
            "refute_each (" ^ exhaustive_num kind ^ ") continuation"
        | Refute_Gen.GenDatatype {constrs, ...} =>
            exhaustive_datatype constrs
        | Refute_Gen.GenFun (domain, range) =>
            (case Refute_Gen.enumerate ty of
               SOME _ => "refute_each " ^ enum_source ty ^ " continuation"
             | NONE => exhaustive_function domain range)
        | Refute_Gen.GenCustom _ => raise Fail "validated custom generator"

      fun exhaustive_declaration (index, ty) =
        (if index = 0 then "fun " else "and ") ^
        generator_name "exh_" ty ^ " continuation size complete =\n  " ^
        exhaustive_body ty

      val exhaustive_generators =
        if null generator_types then ""
        else join "\n" (List.map exhaustive_declaration
          (Lib.enumerate 0 generator_types)) ^ "\n"

      fun floor_for ty = Refute_Gen.own_floor (Refute_Gen.spec_of ty)

      fun random_num kind =
        case kind of
          Refute_Gen.Num =>
            "let val (draw, next) = refute_rand_below " ^
            "(IntInf.fromInt (Int.max (0, size) + 1)) state\n" ^
            "in (" ^ pair "draw"
              (thunk "Refute_EvalSML.num_term draw") ^ ", next) end"
        | Refute_Gen.Int =>
            "let val radius = Int.max (0, size)\n" ^
            "    val (draw, next) = refute_rand_below " ^
            "(IntInf.fromInt (2 * radius + 1)) state\n" ^
            "    val value = draw - IntInf.fromInt radius\n" ^
            "in (" ^ pair "value"
              (thunk "Refute_EvalSML.int_term value") ^ ", next) end"
        | Refute_Gen.Char =>
            "let val (draw, next) = refute_rand_below 256 state\n" ^
            "    val value = Char.chr (IntInf.toInt draw)\n" ^
            "in (" ^ pair "value"
              (thunk "Refute_EvalSML.char_term value") ^ ", next) end"
        | Refute_Gen.Word width =>
            "let val (draw, next) = refute_rand_below " ^
            "(IntInf.pow (2, " ^ integer width ^ ")) state\n" ^
            "in (" ^ pair "draw"
              (thunk ("Refute_EvalSML.word_term " ^ integer width ^
                " draw")) ^ ", next) end"

      fun random_arguments [] [] _ _ _ state continuation =
            continuation ([], state)
        | random_arguments (ty :: tys) (flag :: flags) budget hard_budget
            size state continuation =
            let
              val number = length tys
              val generated = "generated_" ^ integer number
              val next = "state_" ^ integer number
              val call = if flag then generator_name "rnd_aux_" ty ^ " " ^
                "(Int.max (0, " ^ budget ^ " - 1)) " ^
                "(Int.max (0, " ^ hard_budget ^ " - 1)) " ^ size ^ " " ^
                state
                else generator_name "rnd_aux_" ty ^ " " ^
                  "(Int.max (" ^ integer (floor_for ty) ^ ", " ^ budget ^
                  ")) " ^ hard_budget ^ " " ^ size ^ " " ^ state
            in
              "let val (" ^ generated ^ ", " ^ next ^ ") = " ^ call ^
              " in " ^ random_arguments tys flags budget hard_budget
                size next
                (fn (values, final) =>
                  continuation (generated :: values, final)) ^ " end"
            end
        | random_arguments _ _ _ _ _ _ _ =
            raise Fail "Refute_Extract: random argument shape"

      fun random_constructor (constructor, argument_types) flags =
        random_arguments argument_types flags "budget" "hard_budget" "size"
          "next_state" (fn (reversed, final) =>
            let
              val names = reversed
              val values = List.map (fn name =>
                ("#1 " ^ name, "#2 " ^ name)) names
            in
              parens (pair
                (pair (constructor_value constructor values)
                  (constructor_thunk constructor values)) final)
            end)

      fun random_datatype constrs recursive min_size family =
        let
          fun sized_weight flags floors =
            if not (List.exists (fn flag => flag) flags) then "1" else
              let
                val minimum = maximum (ListPair.mapEq
                  (fn (flag, floor) =>
                    if flag then Int.max (0, floor - 1) else 0)
                  (flags, floors))
              in
                if minimum = 0 then "budget"
                else "(if budget > " ^ integer minimum ^
                  " then budget else 0)"
              end
          fun weight ((_, args), flags, floors) =
            let val sized = sized_weight flags floors in
              if List.exists
                   (Refute_Gen.recursive_under_function family) args
              then "(if hard_budget = 0 then 0 else " ^ sized ^ ")"
              else sized
            end
          val rows = ListPair.zip
            (ListPair.zip (constrs, recursive), min_size)
          val weights = List.map (fn ((constr, flags), floors) =>
            weight (constr, flags, floors)) rows
          val total = join " + " weights
          fun select _ [] =
                "(raise Fail \"Refute generated constructor choice\")"
            | select offset (((constructor, flags), _) :: rest) =
                let val current = List.nth (weights, offset)
                    val body = random_constructor constructor flags
                in
                  "if choice < IntInf.fromInt (" ^ current ^ ") then " ^
                  body ^ " else let val choice = choice - " ^
                  "IntInf.fromInt (" ^ current ^ ") in " ^
                  select (offset + 1) rest ^ " end"
                end
        in
          "let val total = " ^ total ^ "\n" ^
          "    val (choice, next_state) =\n" ^
          "      refute_rand_below (IntInf.fromInt total) state\n" ^
          "in " ^ select 0 rows ^ " end"
        end

      fun random_function domain range =
        let
          fun auxiliary ty =
            generator_name "rnd_aux_" ty ^ " (Int.max (" ^
            integer (floor_for ty) ^ ", decayed_size)) " ^
            "decayed_hard_budget decayed_size "
          val domain_random = auxiliary domain
          val range_random = auxiliary range
          val equality = equality_name context domain
          (* Displayed, exactly as in [exhaustive_function] above. *)
          val variable = Term.mk_var ("x", domain)
          val variable_index = raw_index variable
          val enum = Refute_Gen.enumerate domain
          val points = case enum of
              SOME _ => enum_source domain
            | NONE => "draw_points (Int.max (0, size)) after_default []"
          val point_state = case enum of
              SOME _ => "after_default"
            | NONE => "#2 points_result"
          val point_values = case enum of
              SOME _ => points
            | NONE => "rev (#1 points_result)"
        in
          (* [decayed_size] and [decayed_hard_budget] implement the
             function-boundary decay.  Structural budget may still rise to
             the result type's minimum inhabitation floor, but hard
             recursion fuel never does; at 0, a constructor recursive
             beneath a function is disabled while a finite base path
             remains available.  A positive floor therefore cannot
             replenish recursion and create an unbounded branching process.
             [size div 2] and [Int.max (0, size - 1)] agree at sizes 0, 1
             and 2, so this only changes the stream from size 3 up; the
             faster decay avoids the supercritical branching process a
             decay of 1 leaves behind, which routinely exhausts the search
             deadline instead of terminating.  The point count keeps using
             the pre-decay [size]. *)
          "let\n" ^
          "  val decayed_size = size div 2\n" ^
          "  val decayed_hard_budget = hard_budget div 2\n" ^
          "  val (default_generated, after_default) =\n" ^
          "    " ^ range_random ^ "state\n" ^
          "  fun draw_points 0 current points = (points, current)\n" ^
          "    | draw_points count current points =\n" ^
          "      let val (point, next) = " ^ domain_random ^ "current\n" ^
          "      in draw_points (count - 1) next (point :: points) end\n" ^
          (case enum of
             SOME _ => "  val points_result = ([], after_default)\n"
           | NONE => "  val points_result = " ^ points ^ "\n") ^
          "  val points = " ^ point_values ^ "\n" ^
          "  fun values [] current graph updates =\n" ^
          "        ((graph, fn () => Refute_EvalSML.fun_term\n" ^
          "           (Refute_EvalSML.raw_term " ^ integer variable_index ^
          ") ((#2 default_generated) ())\n" ^
          "           (List.map (fn (point, value) =>\n" ^
          "              (point (), value ())) (rev updates))), current)\n" ^
          "    | values ((point, point_term) :: rest) current graph " ^
          "updates =\n" ^
          "      let val ((value, value_term), next) =\n" ^
          "            " ^ range_random ^ "current\n" ^
          "          val graph' = fn x => if " ^ equality ^
          " x point then value else graph x\n" ^
          "      in values rest next graph'\n" ^
          "           ((point_term, value_term) :: updates) end\n" ^
          "  val graph = fn _ => #1 default_generated\n" ^
          "in values points " ^ atom point_state ^ " graph [] end"
        end

      fun random_body ty =
        case Refute_Gen.spec_of ty of
          Refute_Gen.GenEnum values =>
            "let val values = " ^ enum_source ty ^ "\n" ^
            "    val (choice, next) =\n" ^
            "      refute_rand_below " ^ integer (length values) ^
            " state\n" ^
            "in (List.nth (values, IntInf.toInt choice), next) end"
        | Refute_Gen.GenNum kind => random_num kind
        | Refute_Gen.GenDatatype
            {constrs, recursive, min_size, family, ...} =>
            random_datatype constrs recursive min_size family
        | Refute_Gen.GenFun (domain, range) => random_function domain range
        | Refute_Gen.GenCustom _ => raise Fail "validated custom generator"

      fun random_declarations (index, ty) =
        let
          val separator = if index = 0 then "fun " else "and "
          val wrapper = generator_name "rnd_" ty
          val auxiliary = generator_name "rnd_aux_" ty
        in
          separator ^ wrapper ^ " size state =\n" ^
          "  " ^ auxiliary ^ " (Int.max (" ^ integer (floor_for ty) ^
          ", Int.max (0, size))) (Int.max (0, size)) " ^
          "(Int.max (0, size)) state\n" ^
          "and " ^ auxiliary ^ " budget hard_budget size state =\n  " ^
          random_body ty
        end

      val random_generators =
        if null generator_types then ""
        else join "\n" (List.map random_declarations
          (Lib.enumerate 0 generator_types)) ^ "\n"

      fun environment_source environment =
        term_list (List.map (fn (variable, _, term) =>
          parens (integer (raw_index (original_variable variable)) ^
            ", " ^ term)) environment)

      fun substitution_source environment =
        term_list (List.map (fn (variable, _, term) =>
          parens (integer (raw_index variable) ^ ", " ^ term)) environment)

      fun evaluation_thunk tm environment =
        let
          val index = raw_index tm
          val substitutions = substitution_source environment
        in
          thunk ("Refute_EvalSML.eval_term " ^ integer index ^ " " ^
            substitutions)
        end

      fun recovery complete genuine_only fallback =
        parens ("complete := false; if " ^ genuine_only ^
          " then RefuteContinue else " ^ fallback)

      (* Guard-only variant of the above: giving up on a stuck premise
         (the [genuine_only] branch) is a candidate reaching a terminal
         decision without ever reaching Test, so it counts toward
         [candidates_generated], mirroring [Refute_EvalCompute]'s
         [traverse]: every branch that ends a candidate without
         recursing further bumps the counter exactly once.  [Guard]'s
         other terminal branch (the premise evaluating to false, at its
         own call site below) gets the same treatment, as do [Bind],
         [Split], [SmartGuard] and [Enum] inline at their own call
         sites, since none of their branching matches this fallback's
         shape.  [Test] does not need it, since it already increments
         unconditionally on entry and its own stuck path only replaces
         what happens after.  [Prune] is excluded on both substrates:
         the planner already knows that branch can never fire, so
         nothing was generated to count. *)
      fun guard_recovery complete genuine_only fallback =
        parens ("complete := false; if " ^ genuine_only ^ " then " ^
          parens ("candidates_generated := !candidates_generated + 1; " ^
            "RefuteContinue") ^
          " else " ^ fallback)

      fun guard_random_recovery state fallback =
        parens ("complete := false; if genuine_only then " ^
          parens ("candidates_generated := !candidates_generated + 1; " ^
            parens ("RefuteContinue, " ^ state)) ^
          " else " ^ fallback)

      val guard_serial = ref 0

      fun guard_names () =
        let
          val n = (guard_serial := !guard_serial + 1;
            integer (!guard_serial))
        in
          ("refute_guard_" ^ n, "refute_genuine_" ^ n)
        end

      fun evaluated_expression tm =
        let val source = expression context tm
        in #force (context_operations context) source end

      fun safe_value expression failure =
        "(case ((SOME (" ^ expression ^ "))\n" ^
        "       handle Match => NONE\n" ^
        "            | Refute_EvalSML.Stuck _ => NONE) of\n" ^
        "   NONE => " ^ failure ^ "\n" ^
        " | SOME refute_value => "

      (* One Split emitter serves both plan compilers.  An unlisted
         constructor means that the premise which introduced the split is
         false; a stuck scrutinee, however, makes enumeration incomplete. *)
      fun split_case recurse stuck_failure unmatched_failure tm branches
          environment =
        let
          val expression_index = raw_index tm
          val prior_environment = environment
          fun branch_body (constructor, variables, next) =
            let
              val constructor_number = constructor_index constructor
              val additions = List.map (fn (index, variable) =>
                (variable, variable_name variable,
                 thunk ("Refute_EvalSML.split_term " ^
                   integer constructor_number ^ " " ^ integer index ^
                   " " ^ integer expression_index ^ " " ^
                   substitution_source prior_environment)))
                (Lib.enumerate 0 variables)
            in
              recurse next (additions @ environment)
            end
          fun branch (entry as (constructor, variables, _)) =
            constructor_expression context constructor
              (List.map variable_name variables) ^ " => " ^
            branch_body entry
          fun string_entry name =
            List.find (fn (constructor, _, _) =>
              kname constructor = ("list", name)) branches
          fun string_body () =
            let
              val nil_body = case string_entry "NIL" of
                  NONE => unmatched_failure
                | SOME entry => branch_body entry
              val cons_body = case string_entry "CONS" of
                  NONE => unmatched_failure
                | SOME (entry as (_, variables, _)) =>
                    (case List.map variable_name variables of
                       [head, tail] =>
                         "let val " ^ head ^
                         " = " ^ Refute_EvalSML.char_list_head_source
                           "refute_value" ^ "\n" ^
                         "    val " ^ tail ^
                         " = " ^ Refute_EvalSML.char_list_tail_source
                           "refute_value" ^ "\n" ^
                         "in " ^ branch_body entry ^ " end"
                     | _ => reject "malformed string split")
            in
              "if String.size refute_value = 0 then " ^ nil_body ^
              " else " ^ cons_body
            end
          val split_body =
            if is_char_list (Term.type_of tm) then string_body ()
            else "case refute_value of\n" ^
              join "\n | " (List.map branch branches) ^
              "\n | _ => " ^ unmatched_failure
        in
          safe_value (evaluated_expression tm) stuck_failure ^ split_body ^ ")"
        end

      fun enum_name program =
        "smart_enum_" ^ integer
          (Lib.index (same_program program) enum_programs)

      fun generated_from environment tm =
        pair (expression context tm) (evaluation_thunk tm environment)

      val enum_match_serial = ref 0
      fun fresh_enum_match () =
        let val serial = !enum_match_serial
            val _ = enum_match_serial := serial + 1
        in "refute_enum_match_" ^ integer serial end

      fun match_generated terms generated environment success failure =
        let
          val _ = if length terms = length generated then ()
                  else smart_reject "enumerator output arity mismatch"
          val bound = map #1 environment
          fun known seen variable =
            Util.aconv_member variable (bound @ seen)
          fun constructor_result constructor =
            #2 (boolSyntax.strip_fun (Term.type_of constructor))
          fun special_name tm name =
            Term.is_const tm andalso kname tm = name
          fun make_pattern tm value rebuild seen =
            if Term.is_var tm then
              if known seen tm then ("_", [], [], [], seen)
              else
                let val binder = variable_name tm
                in
                  ("_", [], ["val " ^ binder ^ " = " ^ value],
                   [(tm, binder, rebuild)], tm :: seen)
                end
            else if Literal.is_numeral tm orelse
                    intSyntax.is_int_literal tm orelse
                    Literal.is_char_lit tm orelse
                    Literal.is_string_lit tm orelse
                    oneSyntax.is_one tm orelse
                    Term.aconv tm boolSyntax.T orelse
                    Term.aconv tm boolSyntax.F then
              ("_",
               [equality_name context (Term.type_of tm) ^ " " ^
                parens value ^ " " ^ parens (expression context tm)],
               [], [], seen)
            else
              let
                val (constructor, arguments) = boolSyntax.strip_comb tm
              in
                if special_name constructor ("num", "SUC") then
                  (case arguments of
                       [argument] =>
                         let
                           val (pat, guards, bindings, additions, next) =
                             make_pattern argument
                               (parens (value ^ " - 1"))
                               (thunk ("Refute_EvalSML.num_term " ^
                                 parens (value ^ " - 1"))) seen
                         in
                           (pat, value ^ " > 0" :: guards, bindings,
                            additions, next)
                         end
                     | _ => smart_reject "malformed SUC output pattern")
                else if special_name constructor ("num", "ZERO") then
                  ("_", [value ^ " = 0"], [], [], seen)
                else if special_name constructor ("list", "NIL") andalso
                        is_char_list (constructor_result constructor) then
                  ("_", ["String.size " ^ parens value ^ " = 0"],
                   [], [], seen)
                else if special_name constructor ("list", "CONS") andalso
                        is_char_list (constructor_result constructor) then
                  (case arguments of
                       [head, tail] =>
                         let
                           val (head_pat, head_guards, head_bindings,
                                head_additions, after_head) =
                             make_pattern head
                               (Refute_EvalSML.char_list_head_source value)
                               (thunk ("Refute_EvalSML.char_term " ^
                                 parens
                                   (Refute_EvalSML.char_list_head_source
                                     value))) seen
                           val (tail_pat, tail_guards, tail_bindings,
                                tail_additions, after_tail) =
                             make_pattern tail
                               (Refute_EvalSML.char_list_tail_source value)
                               (thunk ("Refute_EvalSML.string_term " ^
                                 parens
                                   (Refute_EvalSML.char_list_tail_source
                                     value))) after_head
                           val _ = (head_pat, tail_pat)
                         in
                           ("_", "String.size " ^ parens value ^ " > 0" ::
                            head_guards @ tail_guards,
                            head_bindings @ tail_bindings,
                            head_additions @ tail_additions, after_tail)
                         end
                     | _ => smart_reject "malformed CONS output pattern")
                else if Term.is_const constructor andalso
                        TypeBase.is_constructor constructor then
                  let
                    val constructor_number = constructor_index constructor
                    val child_names = List.tabulate (length arguments,
                      fn _ => fresh_enum_match ())
                    fun one (((index, argument), child_name),
                        (patterns, guards, bindings, additions,
                         current_seen)) =
                      let
                        val child_term =
                          thunk ("Refute_EvalSML.reconstruction_arg " ^
                            integer constructor_number ^ " " ^ integer index ^
                            " " ^ parens rebuild ^ " ()")
                        val (child_pattern, child_guards, child_bindings,
                             child_additions, next_seen) =
                          make_pattern argument child_name child_term
                            current_seen
                      in
                        (patterns @ [child_pattern], guards @ child_guards,
                         bindings @ child_bindings,
                         additions @ child_additions, next_seen)
                      end
                    val (patterns, guards, bindings, additions, next_seen) =
                      List.foldl one ([], [], [], [], seen)
                        (ListPair.zip (Lib.enumerate 0 arguments, child_names))
                  in
                    (constructor_expression context constructor
                       (ListPair.mapEq (fn (name, pat) =>
                         parens (name ^ " as " ^ pat))
                         (child_names, patterns)),
                     guards, bindings, additions, next_seen)
                  end
                else
                  ("_", [], [], [], seen)
              end
          fun item ((tm, name),
              (patterns, guards, bindings, additions, seen)) =
            let
              val value = "#1 " ^ parens name
              val rebuild = "#2 " ^ parens name
              val (pat, more_guards, more_bindings, more_additions,
                   next_seen) = make_pattern tm value rebuild seen
            in
              (patterns @ [pat], guards @ more_guards,
               bindings @ more_bindings, additions @ more_additions,
               next_seen)
            end
          val (patterns, guards, bindings, additions, _) =
            List.foldl item ([], [], [], [], [])
              (ListPair.zip (terms, generated))
          val values = map (fn name => "#1 " ^ parens name) generated
          val pattern_text =
            case patterns of
                [] => "()"
              | [single] => single
              | _ => parens (join ", " patterns)
          val value_text =
            case values of
                [] => "()"
              | [single] => single
              | _ => parens (join ", " values)
          fun residual (tm, name) =
            equality_name context (Term.type_of tm) ^ " " ^
              parens ("#1 " ^ parens name) ^ " " ^
              parens (expression context tm)
          val residuals = ListPair.mapEq residual (terms, generated)
          fun with_bindings body =
            if null bindings then body
            else "let " ^ join "\n    " bindings ^ "\nin " ^ body ^ " end"
          val checked_success =
            if null residuals then success (additions @ environment)
            else
              safe_value (join " andalso " (map parens residuals)) failure ^
              "if refute_value then " ^ success (additions @ environment) ^
              " else " ^ failure ^ ")"
          (* A char-list head binding contains [String.sub].  It must be
             delayed until after the nonempty guard.  Residual checks, on
             the other hand, can refer to fresh output variables, so run
             them only after [with_bindings] has introduced those names. *)
          val body =
            if null guards then with_bindings checked_success
            else
              safe_value (join " andalso " (map parens guards)) failure ^
              "if refute_value then " ^ with_bindings checked_success ^
              " else " ^ failure ^ ")"
        in
          "(case " ^ value_text ^ " of " ^ pattern_text ^ " => " ^
          body ^ " | _ => " ^ failure ^ ")"
        end

      fun cps_lambda [] body = "(fn () => " ^ body ^ ")"
        | cps_lambda names body =
            List.foldr (fn (name, rest) =>
              "(fn " ^ name ^ " => " ^ rest ^ ")") body names

      fun enum_call_name relation mode =
        let
          val program =
            case List.find (fn ({relation = other, mode = other_mode, ...} :
                Refute_SmartGen.enumerator) =>
              Refute_SmartGen.same_relation relation other andalso
              Refute_SmartGen.eq_mode (mode, other_mode)) enum_programs of
                SOME found => found
              | NONE => reject "smart enumerator dependency is unavailable"
        in
          enum_name program
        end

      fun compile_smart_guard predicate version environment success failure =
        case cached_all_input predicate version of
            NONE => NONE
          | SOME (program, ins) =>
              let
                val generated_inputs = map (generated_from environment) ins
                val fuel = Int.max (0, #depth (#qc config))
                val call = enum_name program ^ " " ^
                  join " " (map parens generated_inputs) ^
                  (if null generated_inputs then "" else " ") ^
                  "(fn () => RefuteGuardSuccess) " ^ integer fuel ^
                  " size complete"
              in
                SOME (parens ("complete := false; case " ^ call ^ " of " ^
                  "RefuteGuardSuccess => " ^ success ^
                  " | _ => " ^ failure))
              end

      fun compile_enum_program program =
        let
          val {mode, clauses, ...} = program
          fun has_input Refute_SmartGen.Input = true
            | has_input (Refute_SmartGen.Pair (left, right)) =
                has_input left orelse has_input right
            | has_input _ = false
          val input_count = length (List.filter has_input
            (Refute_SmartGen.strip_mode mode))
          val formals = List.tabulate (input_count, fn index =>
            "smart_in_" ^ integer index)
          val empty = "RefuteContinue"

          (* pos_bound_cps_bind runs its left operand at [fuel - 1],
             but invokes the following computation at the original fuel.
             Thus only a nested enumerator call receives reduced fuel;
             sequential premises retain the current budget. *)
          fun compile_premises outputs [] environment fuel =
                if null outputs then "continuation ()"
                else "continuation " ^
                  join " "
                    (map (parens o generated_from environment) outputs)
            | compile_premises outputs
                ((Refute_SmartGen.CpsGuard tm) :: rest) environment fuel =
                "if " ^ fuel ^ " <= 0 then " ^ empty ^ " else " ^
                safe_value (evaluated_expression tm) empty ^
                "if refute_value then " ^
                compile_premises outputs rest environment fuel ^
                " else " ^ empty ^ ")"
            | compile_premises outputs
                ((Refute_SmartGen.CpsGenerate variable) :: rest)
                environment fuel =
                let
                  val value = variable_name variable
                  val term = "smart_term_" ^ clean_name value
                  val body = compile_premises outputs rest
                    ((variable, value, term) :: environment) fuel
                  val ty = Term.type_of variable
                  val generated =
                    case Refute_Gen.enumerate ty of
                        SOME _ => "refute_each " ^ enum_source ty ^
                          " (fn (" ^ value ^ ", " ^ term ^ ") => " ^
                          body ^ ")"
                      | NONE =>
                          parens ("complete := false; " ^
                            generator_name "exh_" ty ^ " (fn (" ^ value ^
                            ", " ^ term ^ ") => " ^ body ^
                            ") size complete")
                in
                  "if " ^ fuel ^ " <= 0 then " ^ empty ^ " else " ^
                  generated
                end
            | compile_premises outputs
                ((Refute_SmartGen.CpsCall
                  {rel, mode, ins, outs}) :: rest) environment fuel =
                let
                  val generated_inputs = map (generated_from environment) ins
                  val output_names = List.tabulate (length outs, fn index =>
                    "smart_out_" ^ integer index)
                  fun success extended =
                    compile_premises outputs rest extended fuel
                  val callback = cps_lambda output_names
                    (match_generated outs output_names environment success
                      empty)
                in
                  "if " ^ fuel ^ " <= 0 then " ^ empty ^ " else " ^
                  enum_call_name rel mode ^ " " ^
                  join " " (map parens generated_inputs) ^
                  (if null generated_inputs then "" else " ") ^ callback ^
                  " " ^ parens (fuel ^ " - 1") ^ " size complete"
                end

          fun compile_clause (Refute_SmartGen.CpsClause
                {ins, premises, outs}) =
            let
              fun success environment =
                compile_premises outs premises environment "fuel"
            in
              "if fuel <= 0 then " ^ empty ^ " else " ^
              match_generated ins formals [] success empty
            end

          fun choices [] = empty
            | choices (clause :: rest) =
                "(case " ^ compile_clause clause ^ " of " ^
                "RefuteContinue => " ^ choices rest ^
                " | answer => answer)"
          val keyword = if enum_name program = "smart_enum_0" then "fun "
                        else "and "
        in
          keyword ^ enum_name program ^ " " ^ join " " formals ^
          (if null formals then "" else " ") ^
          "continuation fuel size complete =\n  " ^ choices clauses
        end

      val enum_declarations =
        if null enum_programs then ""
        else
          (case strategy of
               Exhaustive => join "\n" (map compile_enum_program enum_programs)
             | _ => reject
                 "smart generators currently require exhaustive native SML") ^
          "\n"

      fun compile_exhaustive_plan current environment genuine_only =
        case current of
          Prune => "RefuteContinue"
        | Test tm =>
            let
              val hit = "refute_hit (" ^ environment_source environment ^
                ", NONE, NONE, " ^ genuine_only ^ ")"
              val stuck = recovery "complete" "genuine_only"
                ("refute_hit (" ^ environment_source environment ^
                  ", NONE, NONE, false)")
              val assume = "if " ^ genuine_only ^ " then " ^
                "assumption_satisfied := !assumption_satisfied + 1 else ()"
              val conclude = "if " ^ genuine_only ^ " then " ^
                "conclusion_evaluated := !conclusion_evaluated + 1 else ()"
            in
              parens ("tests := !tests + 1; " ^
                "candidates_generated := !candidates_generated + 1; " ^
                assume ^ "; " ^
                "if !tests mod 4096 = 0 then " ^
                "Refute_EvalSML.check_deadline () else (); " ^
                safe_value (evaluated_expression tm) stuck ^
                parens (conclude ^ "; " ^
                  "if refute_value then RefuteContinue else " ^ hit) ^ ")")
            end
        | Guard (tm, next) => guard_body environment genuine_only tm next
        | NegGuard (tm, next) =>
            (* Same three-valued discipline as [Guard]: [tm] is the
               closed complement condition, so a stuck evaluation must
               fall to [stuck] rather than be read as [false]. *)
            guard_body environment genuine_only tm next
        | SmartGuard {predicate, version, cont} =>
            let
              val (name, flag) = guard_names ()
              val body = compile_exhaustive_plan cont environment flag
              val compiled =
                case compile_smart_guard predicate version environment
                    (name ^ " " ^ genuine_only)
                    (parens ("candidates_generated := " ^
                       "!candidates_generated + 1; RefuteContinue")) of
                    SOME source => source
                  | NONE => smart_reject "smart Guard became stale"
            in
              "let fun " ^ name ^ " " ^ flag ^ " = " ^ body ^
              "\nin " ^ compiled ^ " end"
            end
        | Bind (variable, tm, fallback, next) =>
            let
              val value = variable_name variable
              val term = evaluation_thunk tm environment
              val next_environment = (variable, value, term) :: environment
              val continued = compile_exhaustive_plan next next_environment
                genuine_only
              val bump = "candidates_generated := " ^
                "!candidates_generated + 1; RefuteContinue"
              val stuck =
                case fallback of
                    NONE => parens ("complete := false; " ^ bump)
                  | SOME other =>
                      parens ("complete := false; if genuine_only then " ^
                        parens bump ^ " else " ^
                        compile_exhaustive_plan other environment "false")
            in
              safe_value (evaluated_expression tm) stuck ^
              "let val " ^ value ^ " = refute_value\n" ^
              "in " ^ continued ^ " end)"
            end
        | Split (tm, branches) =>
            split_case
              (fn next => fn branch_environment =>
                compile_exhaustive_plan next branch_environment
                  genuine_only)
              (parens ("complete := false; match_failures := " ^
                 "!match_failures + 1; candidates_generated := " ^
                 "!candidates_generated + 1; RefuteContinue"))
              (parens ("candidates_generated := " ^
                 "!candidates_generated + 1; RefuteContinue"))
              tm branches environment
        | Gen (variable, next) =>
            let
              val value = variable_name variable
              val term = "term_" ^ clean_name value
              val ty = Term.type_of variable
              val body = compile_exhaustive_plan next
                ((variable, value, term) :: environment) genuine_only
            in
              case Refute_Gen.enumerate ty of
                SOME _ => "refute_each " ^ enum_source ty ^ " (fn (" ^
                  value ^ ", " ^ term ^ ") => " ^ body ^ ")"
              | NONE =>
                  parens ("complete := false; " ^
                    generator_name "exh_" ty ^ " (fn (" ^ value ^ ", " ^
                    term ^ ") => " ^ body ^ ") size complete")
            end
        | Enum {rel, mode, ins, outs, cont, ...} =>
            let
              val generated_inputs = map (generated_from environment) ins
              val output_names = List.tabulate (length outs, fn index =>
                "plan_smart_out_" ^ integer index)
              fun success extended =
                compile_exhaustive_plan cont extended genuine_only
              val callback = cps_lambda output_names
                (match_generated outs output_names environment success
                  (parens ("candidates_generated := " ^
                     "!candidates_generated + 1; RefuteContinue")))
              val fuel = Int.max (0, #depth (#qc config))
            in
              parens ("complete := false; " ^ enum_call_name rel mode ^ " " ^
                join " " (map parens generated_inputs) ^
                (if null generated_inputs then "" else " ") ^ callback ^
                " " ^ integer fuel ^ " size complete")
            end

      (* Shared by [Guard] and [NegGuard]: both decide a closed
         condition with the same three-valued discipline, and only
         differ in what [tm] means to the caller. *)
      and guard_body environment genuine_only tm next =
        let
          val (name, flag) = guard_names ()
          val body = compile_exhaustive_plan next environment flag
          val stuck = guard_recovery "complete" "genuine_only"
            (name ^ " false")
        in
          "let fun " ^ name ^ " " ^ flag ^ " = " ^ body ^
          "\nin " ^ safe_value (evaluated_expression tm) stuck ^
          "if refute_value then " ^ name ^ " " ^ genuine_only ^
          " else " ^
          parens ("candidates_generated := " ^
            "!candidates_generated + 1; RefuteContinue") ^ ") end"
        end

      fun compile_random_plan current environment genuine state =
        case current of
          Prune => parens ("RefuteContinue, " ^ state)
        | Test tm =>
            let
              val hit = "refute_hit (" ^ environment_source environment ^
                ", NONE, NONE, " ^ genuine ^ ")"
              val stuck = recovery "complete" "genuine_only"
                ("refute_hit (" ^ environment_source environment ^
                  ", NONE, NONE, false)")
              val assume = "if " ^ genuine ^ " then " ^
                "assumption_satisfied := !assumption_satisfied + 1 else ()"
              val conclude = "if " ^ genuine ^ " then " ^
                "conclusion_evaluated := !conclusion_evaluated + 1 else ()"
            in
              parens ("tests := !tests + 1; " ^
                "candidates_generated := !candidates_generated + 1; " ^
                assume ^ "; " ^
                "if !tests mod 4096 = 0 then " ^
                "Refute_EvalSML.check_deadline () else (); " ^
                safe_value (evaluated_expression tm) stuck ^
                parens (conclude ^ "; " ^
                  "if refute_value then RefuteContinue else " ^ hit) ^
                ", " ^ state ^ ")")
            end
        | Guard (tm, next) =>
            let
              val (name, flag) = guard_names ()
              val body = compile_random_plan next environment flag state
              val stuck = guard_random_recovery state (name ^ " false")
            in
              "let fun " ^ name ^ " " ^ flag ^ " = " ^ body ^ "\n" ^
              "in " ^ safe_value (evaluated_expression tm) stuck ^
              "if refute_value then " ^ name ^ " " ^ genuine ^ " else " ^
              parens ("candidates_generated := " ^
                "!candidates_generated + 1; " ^
                parens ("RefuteContinue, " ^ state)) ^ ") end"
            end
        | NegGuard _ =>
            (* [Refute_QC.strategy_run_body] forces smart_generators
               false for every random strategy, and the exhaustive gate
               override only ever selects [Exhaustive], so no random
               plan can carry a [NegGuard]. *)
            smart_reject "Neg Guard reached random compilation"
        | SmartGuard _ =>
            smart_reject "smart Guard reached random compilation"
        | Bind (variable, tm, fallback, next) =>
            let
              val value = variable_name variable
              val term = evaluation_thunk tm environment
              val continued = compile_random_plan next
                ((variable, value, term) :: environment) genuine state
              val bump = "candidates_generated := " ^
                "!candidates_generated + 1; " ^
                parens ("RefuteContinue, " ^ state)
              val failed =
                case fallback of
                    NONE => parens ("complete := false; " ^ bump)
                  | SOME other =>
                      parens ("complete := false; if genuine_only then " ^
                        parens bump ^ " else " ^
                        compile_random_plan other environment "false" state)
            in
              safe_value (evaluated_expression tm) failed ^
              "let val " ^ value ^ " = refute_value in " ^ continued ^
              " end)"
            end
        | Split (tm, branches) =>
            split_case
              (fn next => fn branch_environment =>
                compile_random_plan next branch_environment genuine state)
              (parens
                ("complete := false; match_failures := " ^
                 "!match_failures + 1; candidates_generated := " ^
                 "!candidates_generated + 1; " ^
                 parens ("RefuteContinue, " ^ state)))
              (parens ("candidates_generated := " ^
                 "!candidates_generated + 1; " ^
                 parens ("RefuteContinue, " ^ state)))
              tm branches environment
        | Gen (variable, next) =>
            let
              val value = variable_name variable
              val term = "term_" ^ clean_name value
              val next_state = "state_" ^ clean_name value
              val draw = generator_name "rnd_" (Term.type_of variable) ^
                " size " ^ state
              val body = compile_random_plan next
                ((variable, value, term) :: environment) genuine next_state
            in
              "let val ((" ^ value ^ ", " ^ term ^ "), " ^ next_state ^
              ") = " ^ draw ^ "\nin " ^ body ^ " end"
            end
        | Enum _ =>
            reject "smart generators require exhaustive native SML"

      fun card_declaration (index, plan) =
        let
          val number = index + 1
          val name = "card_" ^ integer number
        in
          case (case strategy of Narrowing => Exhaustive | other => other) of
            Exhaustive =>
              "fun " ^ name ^ " genuine_only size draws state =\n" ^
              "  let val complete = ref " ^
                Bool.toString (not (Refute_Eval.plan_uses_enum plan)) ^ "\n" ^
              "      val tests = ref 0\n" ^
              "      val match_failures = ref 0\n" ^
              "      val assumption_satisfied = ref 0\n" ^
              "      val conclusion_evaluated = ref 0\n" ^
              "      val candidates_generated = ref 0\n" ^
              "      val answer = " ^
                compile_exhaustive_plan plan [] "true" ^ "\n" ^
              "      val hit = case answer of RefuteContinue => NONE\n" ^
              "        | RefuteHit found => SOME found\n" ^
              "  in {hit = hit, complete = !complete,\n" ^
              "      table = refute_table_id, state = state, " ^
              "tests = !tests,\n" ^
              "      match_failures = !match_failures,\n" ^
              "      assumption_satisfied = !assumption_satisfied,\n" ^
              "      conclusion_evaluated = !conclusion_evaluated,\n" ^
              "      candidates_generated = !candidates_generated}\n" ^
              "  end\n"
          | Random _ =>
              "fun " ^ name ^ " genuine_only size draws state =\n" ^
              "  let val complete = ref true\n" ^
              "      val tests = ref 0\n" ^
              "      val match_failures = ref 0\n" ^
              "      val assumption_satisfied = ref 0\n" ^
              "      val conclusion_evaluated = ref 0\n" ^
              "      val candidates_generated = ref 0\n" ^
              "      fun loop 0 current = (NONE, current)\n" ^
              "        | loop remaining current =\n" ^
              "          (case " ^ compile_random_plan plan [] "true"
                "current" ^ " of\n" ^
              "             (RefuteContinue, next) =>\n" ^
              "               loop (remaining - 1) next\n" ^
              "           | (RefuteHit found, next) => (SOME found, next))\n" ^
              "      val (hit, final_state) =\n" ^
              "        loop (Int.max (0, draws)) state\n" ^
              "  in {hit = hit, complete = !complete,\n" ^
              "      table = refute_table_id, state = final_state,\n" ^
              "      tests = !tests, match_failures = !match_failures,\n" ^
              "      assumption_satisfied = !assumption_satisfied,\n" ^
              "      conclusion_evaluated = !conclusion_evaluated,\n" ^
              "      candidates_generated = !candidates_generated}\n" ^
              "  end\n"
          | Narrowing => raise Fail "normalized narrowing strategy"
        end

      val _ = List.app (fn plan =>
        let
          fun payload current =
            case current of
              Test tm => ignore (expression context tm)
            | Gen (_, next) => payload next
            | Bind (_, tm, fallback, next) =>
                (ignore (expression context tm);
                 Option.app payload fallback; payload next)
            | Split (tm, branches) =>
                (ignore (expression context tm);
                 List.app (payload o #3) branches)
            | Guard (tm, next) =>
                (ignore (expression context tm); payload next)
            | NegGuard (tm, next) =>
                (ignore (expression context tm); payload next)
            | SmartGuard {cont, ...} => payload cont
            | Enum {ins, cont, ...} =>
                (List.app (ignore o expression context) ins; payload cont)
            | Prune => ()
        in payload plan end) plans
      val cards = String.concat
        (List.map card_declaration (Lib.enumerate 0 plans))
      val table_id = Refute_EvalSML.register_term_tables
        (rev (!(#list constructor_terms))) (rev (!(#list raw_terms)))
      fun finish () =
        let
          val table_declaration =
            "val refute_table_id = " ^ integer table_id ^ "\n"
          val card_names = List.map (fn index =>
            "card_" ^ integer (index + 1))
            (List.tabulate (length plans, fn x => x))
          val dispatch =
            "val test_cards = Vector.fromList [" ^
            join ", " card_names ^ "]\n" ^
            "fun dispatch card genuine_only size draws state =\n" ^
            "  Vector.sub (test_cards, card - 1)\n" ^
            "    genuine_only size draws state\n" ^
            "fun protected_dispatch card genuine_only size draws state =\n" ^
            "  Refute_EvalSML.with_term_tables refute_table_id (fn () =>\n" ^
            "    let val answer = dispatch card genuine_only size " ^
            "draws state\n" ^
            "        val hit = Option.map\n" ^
            "          (fn (environment, grounding, case_tree, genuine) =>\n" ^
            "          (List.map (fn (index, rebuild) =>\n" ^
            "             (index, Refute_EvalSML.wrap_reconstruction\n" ^
            "               refute_table_id rebuild)) environment,\n" ^
            "           Option.map (List.map (fn (index, rebuild) =>\n" ^
            "             (index, Refute_EvalSML.wrap_reconstruction\n" ^
            "               refute_table_id rebuild))) grounding,\n" ^
            "           case_tree, genuine))\n" ^
            "          (#hit answer)\n" ^
            "    in {hit = hit, complete = #complete answer,\n" ^
            "        table = refute_table_id, state = #state answer,\n" ^
            "        tests = #tests answer,\n" ^
            "        match_failures = #match_failures answer,\n" ^
            "        assumption_satisfied = #assumption_satisfied answer,\n" ^
            "        conclusion_evaluated = #conclusion_evaluated answer,\n" ^
            "        candidates_generated = " ^
              "#candidates_generated answer}\n" ^
            "    end)\n" ^
            "fun install () =\n" ^
            "  Refute_EvalSML.installed_dispatch := SOME protected_dispatch\n"
          val _ = drain_definitions context
          val source = source_prefix context ^
            definition_declarations context ^ "\n" ^
            generator_runtime ^ "\n" ^ exhaustive_generators ^
            random_generators ^ enum_declarations ^ table_declaration ^
            cards ^ dispatch
        in
          {source = source, entry = "install ()", table = table_id}
        end
    in
      finish ()
      handle error =>
        let
          val cleanup_result = Exn.capture
            Refute_EvalSML.unregister_term_tables table_id
        in
          case (error, cleanup_result) of
              (Interrupt, _) => raise Interrupt
            | (_, Exn.Exn Interrupt) => raise Interrupt
            | _ => Exn.reraise error
        end
    end

  (* Adds an idempotent owner close over extract_tests_with Strict, so a
     caller can release the vectors retained by generated code. *)
  fun extract_tests config strategy plans =
    let
      val {source, entry, table} =
        extract_tests_with Strict config strategy plans
      val closed = ref false
      fun close () =
        if !closed then ()
        else (closed := true; Refute_EvalSML.unregister_term_tables table)
    in
      {source = source, entry = entry, table = table, close = close}
    end

  (* Compile the first-order bridge between generic narrowing terms and the
     lazy extracted property.  Shapes and search live in Refute_Narrow; only
     these heterogeneously typed conversion functions must be generated. *)
  fun extract_narrowing_window (config : Refute_Core.config) {first, last}
        prefix body =
    let
      val _ =
        if first >= 0 andalso last >= first then ()
        else reject "invalid narrowing depth window"
      val context = new_context Lazy
      val constructor_terms =
        {list = ref ([] : term list), count = ref 0,
         indexes = ref (Redblackmap.mkDict Term.compare)}
      val raw_terms =
        {list = ref ([] : term list), count = ref 0,
         indexes = ref (Redblackmap.mkDict Term.compare)}

      fun index_term {list, count, indexes} tm =
        case Redblackmap.peek (!indexes, tm) of
            SOME index => index
          | NONE =>
              let
                val index = !count
                val _ = indexes := Redblackmap.insert (!indexes, tm, index)
                val _ = list := tm :: !list
                val _ = count := index + 1
              in
                index
              end
      fun constructor_index tm = index_term constructor_terms tm
      fun raw_index tm = index_term raw_terms tm
      fun term_list values = "[" ^ join ", " values ^ "]"

      (* Finitization belongs to the narrowing instance, after prenexing but
         before extraction.  Keep the original binders as environment keys;
         reconstructed descriptions are converted back to those types. *)
      val originals = map #2 prefix
      val (prefix, body) =
        if #finite_functions (#qc config) then
          Refute_Narrow.finitize_functions (prefix, body)
        else
          (prefix, body)
      val transformed = map #2 prefix
      val safe = List.map (fn (index, variable) =>
        Term.mk_var ("refute_bound_" ^ integer index,
          Term.type_of variable)) (Lib.enumerate 0 transformed)
      val substitution = ListPair.mapEq (fn (old, fresh) =>
        {redex = old, residue = fresh}) (transformed, safe)
      val body = Term.subst substitution body
      val prefix = ListPair.mapEq (fn ((quantifier, _), variable) =>
        (quantifier, variable)) (prefix, safe)

      (* The brackets are load-bearing: an unbracketed [handle] binds to the
         last arm of the [case], not to its scrutinee, which is what raises
         here.  Without them the refusal below is dead and the missing
         generator escapes as an exception instead. *)
      fun dependencies ty =
        (case Refute_Gen.spec_of ty of
             Refute_Gen.GenDatatype {constrs, ...} =>
               List.concat (map #2 constrs)
           | Refute_Gen.GenFun _ =>
               reject ("narrowing cannot generate function type " ^
                 type_name ty ^ " before finitization")
           | Refute_Gen.GenCustom (_, {enumerate = SOME _, ...}) => []
           | Refute_Gen.GenCustom _ =>
               reject ("narrowing custom generator for " ^ type_name ty ^
                 " has no exhaustive enumeration")
           | _ => [])
        handle Refute_Gen.NoGenerator (missing, reason) =>
          reject ("no narrowing generator for " ^ type_name missing ^
            " — " ^ reason)

      fun close_types [] seen = rev seen
        | close_types (ty :: rest) seen =
            if Util.member_type ty seen then
              close_types rest seen
            else
              close_types (dependencies ty @ rest) (ty :: seen)
      val types = close_types (map (Term.type_of o #2) prefix) []
      val _ = List.app (fn ty => ignore (ensure_type context ty)) types
      val _ = ignore (ensure_type context Type.bool)
      val shape_memo = Refute_Narrow.new_shape_memo ()

      fun checked_shape depth ty =
        Refute_Narrow.shape_of_with shape_memo depth ty
        handle Refute_Narrow.ShapeFailure (offending_ty, reason) =>
          reject (Refute_Narrow.inapplicable_message offending_ty reason)

      (* Freeze every depth's shape while extracting.  Generated search shapes
         contain only local IDs and product structure.  The exact alternatives
         stay in these meta-level rows and generate an immutable compile-local
         reconstruction case; no custom enumerator is called at run time. *)
      val shape_rows = List.tabulate (last - first + 1, fn index =>
        map (checked_shape (first + index)) types)

      fun type_index ty = Lib.index (Util.same_type ty) types
      fun shapes_of ty = map (fn row =>
        List.nth (row, type_index ty)) shape_rows
      fun argument_types ty id =
        case Refute_Gen.spec_of ty of
            Refute_Gen.GenDatatype {constrs, ...} =>
              #2 (List.nth (constrs, id))
          | _ => []
      fun exact_entries_in target_ty ty
            (shape as Refute_Narrow.Narrowing_sum_of_products
              {depth, alternatives, ...}) =
        let
          fun one alternative =
            (if Util.same_type target_ty ty then
               case #exact alternative of
                   SOME value => [((depth, #id alternative), value)]
                 | NONE => []
             else []) @
            List.concat (ListPair.mapEq (fn (arg_ty, argument) =>
              exact_entries_in target_ty arg_ty argument)
              (argument_types ty (#id alternative), #arguments alternative))
        in
          List.concat (map one alternatives)
        end
      fun exact_entries_of ty =
        List.rev (List.foldl (fn (entry as ((depth, id), _), result) =>
          if List.exists (fn ((other_depth, other_id), _) =>
               depth = other_depth andalso id = other_id) result then result
          else entry :: result) []
          (List.concat (map (fn row =>
            List.concat (ListPair.mapEq (fn (row_ty, shape) =>
              exact_entries_in ty row_ty shape) (types, row)))
            shape_rows)))
      fun conv_name ty = "narrow_conv_" ^ integer (type_index ty)
      fun recon_name ty = "narrow_recon_" ^ integer (type_index ty)
      fun replay_recon_name ty =
        "narrow_replay_recon_" ^ integer (type_index ty)
      val witnesses = List.map (fn (index, ty) =>
        Term.mk_var ("refute_narrow_type_" ^ integer index, ty))
        (Lib.enumerate 0 types)
      fun witness_index ty = raw_index (List.nth (witnesses, type_index ty))

      fun around_zero index =
        "(if " ^ index ^ " = 0 then 0 else if " ^ index ^
        " mod 2 = 1 then (" ^ index ^ " + 1) div 2 else ~(" ^
        index ^ " div 2))"

      fun primitive_value kind index =
        case kind of
            Refute_Gen.Num => lazy_delay ("IntInf.fromInt " ^ index)
          | Refute_Gen.Int =>
              lazy_delay ("IntInf.fromInt " ^ around_zero index)
          | Refute_Gen.Char => lazy_delay ("Char.chr " ^ index)
          | Refute_Gen.Word _ =>
              lazy_delay ("IntInf.fromInt " ^ index)

      fun constructor_pattern index arguments =
        "(" ^ integer index ^ ", " ^
        term_list arguments ^ ")"

      fun exact_case render ty =
        let
          fun branch ((depth, id), value) =
            "(" ^ integer depth ^ ", " ^ integer id ^ ") => " ^
            render value
          val branches = map branch (exact_entries_of ty)
        in
          if null branches then "raise Match"
          else "(case (depth, constructor) of\n       " ^
            join "\n     | " branches ^ "\n     | _ => raise Match)"
        end

      fun conversion_case ty =
        case Refute_Gen.spec_of ty of
            Refute_Gen.GenEnum values =>
              "List.nth (" ^ term_list (map (expression context) values) ^
              ", constructor)"
          | Refute_Gen.GenNum kind => primitive_value kind "constructor"
          | Refute_Gen.GenDatatype {constrs, ...} =>
              let
                fun branch (index, (constructor, argument_types)) =
                  let
                    val arguments = List.tabulate (length argument_types,
                      fn number => "argument_" ^ integer number)
                    val converted = ListPair.mapEq (fn (argument, arg_ty) =>
                      conv_name arg_ty ^
                      " (Int.max (0, depth - 1)) " ^ argument)
                      (arguments, argument_types)
                  in
                    constructor_pattern index arguments ^ " => " ^
                    constructor_expression context constructor converted
                  end
              in
                "(case (constructor, arguments) of\n" ^
                join "\n       | " (map branch (Lib.enumerate 0 constrs)) ^
                "\n       | _ => raise Match)"
              end
          | Refute_Gen.GenCustom (_, {enumerate = SOME _, ...}) =>
              exact_case (expression context) ty
          | _ => raise Fail "validated narrowing conversion"

      fun reconstruction_case recurse ty =
        let
          fun exact () =
            exact_case (fn value =>
              "Refute_EvalSML.raw_term " ^ integer (raw_index value)) ty
        in
          case Refute_Gen.spec_of ty of
            Refute_Gen.GenEnum _ => exact ()
          | Refute_Gen.GenNum _ => exact ()
          | Refute_Gen.GenDatatype {constrs, ...} =>
              let
                fun branch (index, (constructor, argument_types)) =
                  let
                    val arguments = List.tabulate (length argument_types,
                      fn number => "argument_" ^ integer number)
                    val rebuilt = ListPair.mapEq (fn (argument, arg_ty) =>
                      recurse arg_ty ^
                      " (Int.max (0, depth - 1)) " ^ argument)
                      (arguments, argument_types)
                  in
                    constructor_pattern index arguments ^ " => " ^
                    "Refute_EvalSML.con_term " ^
                    integer (constructor_index constructor) ^ " " ^
                    term_list rebuilt
                  end
              in
                "(case (constructor, arguments) of\n" ^
                join "\n       | " (map branch (Lib.enumerate 0 constrs)) ^
                "\n       | _ => raise Match)"
              end
          | Refute_Gen.GenCustom (_, {enumerate = SOME _, ...}) => exact ()
          | _ => raise Fail "validated narrowing reconstruction"
        end

      fun narrow_declaration {name_of, variable_arm, body} (index, ty) =
        (if index = 0 then "fun " else "and ") ^ name_of ty ^
        " depth narrowing_term =\n  case narrowing_term of\n" ^
        "      Refute_Narrow.Narrowing_variable " ^ variable_arm ty ^ "\n" ^
        "    | Refute_Narrow.Narrowing_constructor " ^
        "(constructor, arguments) =>\n        " ^ body ty

      val conversion_declaration = narrow_declaration
        {name_of = conv_name,
         variable_arm = fn _ =>
           "(position, _) =>\n        Refute_EvalSML.lazy_hole position",
         body = conversion_case}

      val reconstruction_declaration = narrow_declaration
        {name_of = recon_name,
         variable_arm = fn ty =>
           "_ =>\n        Refute_EvalSML.hole_term " ^
           integer (witness_index ty),
         body = reconstruction_case recon_name}

      val replay_reconstruction_declaration = narrow_declaration
        {name_of = replay_recon_name,
         variable_arm = fn ty =>
           "(position, _) =>\n        Refute_EvalSML.replay_variable " ^
           integer (witness_index ty) ^ " position",
         body = reconstruction_case replay_recon_name}

      fun shape_name depth ty =
        "narrow_shape_" ^ integer depth ^ "_" ^ integer (type_index ty)

      fun shape_source row_depth ty
            (Refute_Narrow.Narrowing_sum_of_products
              {depth, complete, syntactic_complete, alternatives}) =
        let
          val _ =
            if depth = row_depth then ()
            else raise Fail "narrowing shape depth mismatch"
          val _ =
            if row_depth < 0 then
              raise Fail "negative narrowing shape depth"
            else ()
          fun alternative_source {id, arguments, ...} =
            let
              val argument_types = argument_types ty id
              val _ =
                if length argument_types = length arguments then ()
                else raise Fail "narrowing shape argument mismatch"
              val _ =
                if null arguments orelse row_depth > 0 then ()
                else raise Fail "narrowing shape underflow"
            in
              "{id = " ^ integer id ^ ", exact = NONE" ^
              ", arguments = " ^
              term_list
                (map (shape_name (row_depth - 1)) argument_types) ^ "}"
            end
        in
          "Refute_Narrow.Narrowing_sum_of_products " ^
          "{depth = " ^ integer depth ^
          ", complete = " ^ Bool.toString complete ^
          ", syntactic_complete = " ^
          Bool.toString syntactic_complete ^
          ", alternatives = " ^
          term_list (map alternative_source alternatives) ^ "}"
        end

      fun shape_binding depth (ty, shape) =
        "val " ^ shape_name depth ty ^ " =\n  " ^
        shape_source depth ty shape ^ "\n"
      fun add_shape ty
            (shape as Refute_Narrow.Narrowing_sum_of_products
              {depth, alternatives, ...}) result =
        if List.exists (fn (other_depth, other_ty, _) =>
             depth = other_depth andalso Util.same_type ty other_ty)
             result then result
        else
          let
            fun add_alternative (alternative, result) =
              ListPair.foldlEq (fn (arg_ty, argument, accumulated) =>
                add_shape arg_ty argument accumulated) result
                (argument_types ty (#id alternative),
                 #arguments alternative)
          in
            List.foldl add_alternative ((depth, ty, shape) :: result)
              alternatives
          end
      val distinct_shapes = List.foldl (fn (row, result) =>
        ListPair.foldlEq (fn (ty, shape, accumulated) =>
          add_shape ty shape accumulated) result (types, row)) [] shape_rows
      fun shape_entry_compare ((left, _, _), (right, _, _)) =
        Int.compare (left, right)
      val shape_bindings =
        join "" (map (fn (depth, ty, shape) =>
          shape_binding depth (ty, shape))
          (Listsort.sort shape_entry_compare distinct_shapes))
      fun shape_row_source depth =
        "Vector.fromList " ^ term_list (map (shape_name depth) types)
      val shape_declaration =
        shape_bindings ^
        "val narrow_shape_rows = Vector.fromList " ^
        term_list (map shape_row_source
          (List.tabulate (last - first + 1, fn index => first + index))) ^
        "\n" ^
        "fun narrow_shape depth type_index =\n" ^
        "  Vector.sub (Vector.sub (narrow_shape_rows, depth - " ^
        integer first ^ "), " ^
        "type_index)\n"
      val conversions = join "\n"
        (map conversion_declaration (Lib.enumerate 0 types)) ^ "\n"
      val reconstructions = join "\n"
        (map reconstruction_declaration (Lib.enumerate 0 types)) ^ "\n" ^
        join "\n" (map replay_reconstruction_declaration
          (Lib.enumerate 0 types)) ^ "\n"

      val body_expression = expression context body
      fun binding grounded (index, ((_, variable), original)) =
        let
          val ty = Term.type_of variable
          val original_index = raw_index original
          val argument = "List.nth (arguments, " ^ integer index ^ ")"
          val narrowing_term =
            if grounded then
              "valOf (Refute_Narrow.first_completion " ^
              "(narrow_shape depth " ^ integer (type_index ty) ^
              ") (" ^ argument ^ "))"
            else argument
          val rebuilt = recon_name ty ^ " depth (" ^ narrowing_term ^ ")"
        in
          "(" ^ integer original_index ^ ", fn () => " ^
          (if #finite_functions (#qc config) then
             "Refute_Narrow.eval_finite_functions_as " ^
             "(Term.type_of (Refute_EvalSML.raw_term " ^
             integer original_index ^ ")) (" ^ rebuilt ^ ")"
           else rebuilt) ^ ")"
        end
      val has_existential = List.exists
        (fn (Refute_Eval.Exists, _) => true | _ => false) prefix
      val leading_count =
        let
          fun count total ((Refute_Eval.Forall, _) :: rest) =
                count (total + 1) rest
            | count total _ = total
        in
          count 0 prefix
        end
      val reported_prefix =
        if has_existential then
          List.take (ListPair.zip (prefix, originals), leading_count)
        else ListPair.zip (prefix, originals)
      val indexed_prefix = Lib.enumerate 0 reported_prefix
      val bindings = map (binding false) indexed_prefix
      val ground_bindings = map (binding true) indexed_prefix
      fun groundable (index, ((_, variable), _)) =
        "Option.isSome (Refute_Narrow.first_completion " ^
        "(narrow_shape depth " ^
        integer (type_index (Term.type_of variable)) ^ ") " ^
        "(List.nth (arguments, " ^ integer index ^ ")))"
      val groundability = map groundable indexed_prefix
      val environment_source = term_list bindings
      val ground_environment_source =
        if null groundability then "SOME []"
        else "if " ^ join " andalso " groundability ^ " then SOME (" ^
          term_list ground_bindings ^ ") else NONE"
      fun replay_binding (index, ((_, variable), original)) =
        let
          val ty = Term.type_of variable
          val rebuilt = replay_recon_name ty ^
            " depth narrowing_term"
        in
          integer index ^ " => " ^
          (if #finite_functions (#qc config) then
             "Refute_Narrow.eval_finite_functions_as " ^
             "(Term.type_of (Refute_EvalSML.raw_term " ^
             integer (raw_index original) ^ ")) (" ^ rebuilt ^ ")"
           else rebuilt)
        end
      val replay_branches = map replay_binding
        (Lib.enumerate 0 (ListPair.zip (prefix, originals)))
      val replay_rebuild =
        if null replay_branches then
          "fun replay_rebuild depth index narrowing_term =\n" ^
          "  raise Subscript\n"
        else
          "fun replay_rebuild depth index narrowing_term =\n" ^
          "  case index of\n      " ^
          join "\n    | " replay_branches ^
          "\n    | _ => raise Subscript\n"
      val argument_values = map (fn (index, (_, variable)) =>
        conv_name (Term.type_of variable) ^
        " depth (List.nth (arguments, " ^ integer index ^ "))")
        (Lib.enumerate 0 prefix)
      val shapes = map (fn (_, variable) =>
        "narrow_shape depth " ^
        integer (type_index (Term.type_of variable))) prefix
      val initial_arguments = term_list (map (fn (index, shape) =>
        "Refute_Narrow.Narrowing_variable ([" ^ integer index ^
        "], " ^ shape ^ ")") (Lib.enumerate 0 shapes))
      fun quantifier_source (Refute_Eval.Forall, _) =
            "Refute_Narrow.Universal"
        | quantifier_source (Refute_Eval.Exists, _) =
            "Refute_Narrow.Existential"
      val tree_prefix = term_list (ListPair.mapEq (fn (entry, shape) =>
        "(" ^ quantifier_source entry ^ ", " ^ shape ^ ")")
        (prefix, shapes))
      val _ = if has_existential andalso
          not (#allow_existentials (#qc config)) then
          reject "narrowing existential goals require allow_existentials"
        else ()

      (* Lazy primitive failures are the native analogue of upstream's
         PatternMatchFail.  Like generated non-exhaustive matches, they taint
         the result instead of escaping the narrowing engine. *)
      val evaluate =
        "fun narrow_evaluate depth genuine_only arguments =\n" ^
        "  let\n" ^
        join "\n" (map (fn (index, value) =>
          "    val " ^ variable_name (#2 (List.nth (prefix, index))) ^
          " = " ^ value) (Lib.enumerate 0 argument_values)) ^
        (if null prefix then "" else "\n") ^
        "  in\n    (Refute_EvalSML.check_deadline ();\n" ^
        "     Refute_Narrow.Known {genuine = true, result =\n" ^
        "       Susp.force (" ^ body_expression ^ ")})\n" ^
        "    handle Refute_EvalSML.Hole position =>\n" ^
        "      Refute_Narrow.NeedsRefinement position\n" ^
        "         | Match => Refute_Narrow.Known\n" ^
        "             {genuine = false, result = genuine_only}\n" ^
        "         | Refute_EvalSML.Stuck _ => Refute_Narrow.Known\n" ^
        "             {genuine = false, result = genuine_only}\n" ^
        "  end\n"

      val engine =
        if has_existential then
          "val initial = Refute_Narrow.tree_of " ^ tree_prefix ^ "\n" ^
          "val result = Refute_Narrow.refute_pnf_avoiding genuine_only\n" ^
          "  depth (narrow_evaluate depth)\n" ^
          "  (fn {genuine, example, ...} =>\n" ^
          "    let\n" ^
          "      val arguments = Refute_Narrow.leading_universals " ^
          integer leading_count ^ " example\n" ^
          "      val replay = Refute_Narrow.replay_of_example\n" ^
          "        (replay_rebuild depth) example\n" ^
          "    in not ((!Refute_EvalSML.ignored_filter)\n" ^
          "      (candidate depth arguments (SOME replay) genuine)) end)\n" ^
          "  initial\n" ^
          "val (hit, tests, decided, complete) =\n" ^
          "  case result of\n" ^
          "      Refute_Narrow.PnfCounterexample\n" ^
          "        {genuine, example, tests, decided, ...} =>\n" ^
          "        let\n" ^
          "          val arguments = Refute_Narrow.leading_universals " ^
          integer leading_count ^ " example\n" ^
          "          val replay = Refute_Narrow.replay_of_example\n" ^
          "            (replay_rebuild depth) example\n" ^
          "        in (SOME (candidate depth arguments (SOME replay) genuine),\n" ^
          "            tests, decided, false) end\n" ^
          "    | Refute_Narrow.PnfExhausted {tests, decided, complete, ...} =>\n" ^
          "        (NONE, tests, decided, complete)\n"
        else
          "val result = Refute_Narrow.refute_plain_avoiding genuine_only\n" ^
          "  {arguments = " ^ initial_arguments ^ ",\n" ^
          "   evaluate = narrow_evaluate depth,\n" ^
          "   accept = accept_hit depth genuine_only}\n" ^
          "val (hit, tests, decided, complete) =\n" ^
          "  case result of\n" ^
          "      Refute_Narrow.PlainCounterexample\n" ^
          "        {genuine, arguments, tests, decided} =>\n" ^
          "        (make_hit depth arguments NONE genuine, tests, decided,\n" ^
          "         false)\n" ^
          "    | Refute_Narrow.PlainExhausted {tests, decided, complete} =>\n" ^
          "        (NONE, tests, decided, complete)\n"

      val table_id = Refute_EvalSML.register_term_tables
        (rev (!(#list constructor_terms))) (rev (!(#list raw_terms)))
      fun finish () =
        let
          val _ = drain_definitions context
          val runtime =
            "val refute_table_id = " ^ integer table_id ^ "\n" ^
            replay_rebuild ^
            "fun candidate depth arguments case_tree genuine =\n" ^
            "  (" ^ environment_source ^ ", " ^
            ground_environment_source ^ ", case_tree, genuine)\n" ^
            "fun accept_hit depth genuine_only arguments genuine =\n" ^
            "  (not genuine_only orelse Refute_Narrow.all_ground arguments)\n" ^
            "  andalso not ((!Refute_EvalSML.ignored_filter)\n" ^
            "    (candidate depth arguments NONE genuine))\n" ^
            "fun make_hit depth arguments case_tree genuine =\n" ^
            "  let val found = candidate depth arguments case_tree genuine\n" ^
            "  in if (!Refute_EvalSML.ignored_filter) found then NONE\n" ^
            "     else SOME found\n  end\n" ^
            "fun dispatch card genuine_only depth draws state =\n" ^
            "  if card <> 1 then raise Subscript else\n" ^
            "  let\n    " ^ engine ^
            "  in {hit = hit, complete = complete, table = refute_table_id,\n" ^
            "      state = state, tests = tests, match_failures = 0,\n" ^
            (* Narrowing evaluates one combined prenex formula per
               candidate, so it has no separate assumption/conclusion
               phase -- but [tests] still conflates decided rows
               ([Known]) with rows that only got refined further
               ([NeedsRefinement]).  [decided] is the honest count of
               the former; [tests] is every attempt, decided or not, so
               it is the candidates_generated denominator. *)
            "      assumption_satisfied = decided,\n" ^
            "      conclusion_evaluated = decided,\n" ^
            "      candidates_generated = tests}\n" ^
            "  end\n" ^
            "fun protected_dispatch card genuine_only depth draws state =\n" ^
            "  Refute_EvalSML.with_term_tables refute_table_id (fn () =>\n" ^
            "    let val answer = dispatch card genuine_only depth " ^
            "draws state\n" ^
            "        val hit = Option.map\n" ^
            "          (fn (environment, grounding, case_tree, genuine) =>\n" ^
            "          (List.map (fn (index, rebuild) =>\n" ^
            "             (index, Refute_EvalSML.wrap_reconstruction\n" ^
            "               refute_table_id rebuild)) environment,\n" ^
            "           Option.map (List.map (fn (index, rebuild) =>\n" ^
            "             (index, Refute_EvalSML.wrap_reconstruction\n" ^
            "               refute_table_id rebuild))) grounding,\n" ^
            "           case_tree, genuine))\n" ^
            "          (#hit answer)\n" ^
            "    in {hit = hit, complete = #complete answer,\n" ^
            "        table = refute_table_id, state = #state answer,\n" ^
            "        tests = #tests answer,\n" ^
            "        match_failures = #match_failures answer,\n" ^
            "        assumption_satisfied = #assumption_satisfied answer,\n" ^
            "        conclusion_evaluated = #conclusion_evaluated answer,\n" ^
            "        candidates_generated = " ^
              "#candidates_generated answer}\n" ^
            "    end)\n" ^
            "fun install () = Refute_EvalSML.installed_dispatch :=\n" ^
            "  SOME protected_dispatch\n"
          val source = source_prefix context ^
            definition_declarations context ^ "\n" ^ shape_declaration ^
            conversions ^ reconstructions ^ evaluate ^ runtime
        in
          {source = source, entry = "install ()", table = table_id}
        end
    in
      finish ()
      handle error =>
        let
          val cleanup = Exn.capture
            Refute_EvalSML.unregister_term_tables table_id
        in
          case (error, cleanup) of
              (Interrupt, _) => raise Interrupt
            | (_, Exn.Exn Interrupt) => raise Interrupt
            | _ => Exn.reraise error
        end
    end

  val active_narrowing_window :
    {first : int, last : int} Thread_Data.var = Thread_Data.var ()

  fun with_narrowing_window window f argument =
    Thread_Data.setmp active_narrowing_window (SOME window) f argument

  fun extract_narrowing config prefix body =
    let
      val window =
        case Thread_Data.get active_narrowing_window of
            SOME selected => selected
          | NONE =>
              {first = 0, last = Int.max (0, #size (#qc config))}
    in
      extract_narrowing_window config window prefix body
    end

  (* Plan extraction is the substrate compile itself.  Preflight contributes
     only validation of evaluation terms, which are not executable plan
     nodes and therefore cannot use the smart-Guard relation exception. *)
  fun native_preflight _ _ _ evals =
    let
      fun validate_eval tm =
        let
          val constants = Refute_Core.nonexecutable_constants [tm]
          val binders = HolKernel.find_terms Term.is_abs tm
          val _ =
            if null binders then ()
            else raise NotExtractable
              ["native preflight eval contains an unexpanded binder"]
          val _ =
            if null constants then ()
            else raise NotExtractable
              ["native preflight eval is nonexecutable: " ^
               Refute_Core.show_constants constants]
        in
          ignore (extract_term tm)
        end

    in
      (List.app validate_eval evals; [])
    end
    handle Interrupt => raise Interrupt
         | NotExtractable reasons => reasons
         | error =>
             ["native preflight: " ^
              (case General.exnMessage error of
                   "" => "unknown validation exception"
                 | text => text)]

  fun extract_problem extraction_mode config strategy problem =
    let
      val mode = case extraction_mode of
          Refute_EvalSML.StrictExtraction => Strict
        | Refute_EvalSML.LazyExtraction => Lazy
      val extracted = case problem of
          Refute_Eval.Plans plans =>
            extract_tests_with mode config strategy plans
        | Refute_Eval.Pnf {prefix, body} =>
            extract_narrowing config prefix body
    in
      Refute_EvalSML.Extracted extracted
    end
    handle NotExtractable reasons =>
             Refute_EvalSML.ExtractionFailed reasons
         | Interrupt => raise Interrupt
end
