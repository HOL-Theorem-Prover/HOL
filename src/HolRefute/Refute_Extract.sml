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

  fun clean_name name =
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

  fun upper_name name = "C_" ^ clean_name name
  fun lower_name name = "f_" ^ clean_name name

  fun same_term left right = Term.compare (left, right) = EQUAL

  fun kname tm =
    let val {Thy, Name, ...} = Term.dest_thy_const tm
    in (Thy, Name) end

  fun kname_text (thy, name) = thy ^ "$" ^ name

  fun quote text = Portable.mlquote text

  val join = String.concatWith

  fun parens text = "(" ^ text ^ ")"

  fun intinf_literal text =
    "(valOf (IntInf.fromString " ^ quote text ^ ") : IntInf.int)"

  fun num_literal number = intinf_literal (Arbnum.toString number)
  fun int_literal integer =
    let val text = Arbint.toString integer
    in intinf_literal (String.substring (text, 0, String.size text - 1)) end

  fun type_name ty =
    Hol_pp.type_to_string ty
    handle _ => "<unknown type>"

  fun reject message = raise NotExtractable [message]

  type datatype_desc =
    { hol_ty : hol_type,
      ml_name : string,
      constructors : (term * hol_type list * string) list }

  type context =
    { mode : extraction_mode,
      datatypes : datatype_desc list ref,
      types : (hol_type * ml_ty * string) list ref,
      equalities : hol_type list ref,
      definitions : (term * string * Thm.thm) list ref,
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

  fun is_lazy ({mode, ...} : context) = mode = Lazy

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

  fun is_char_list ty = Util.same_type ty stringSyntax.string_ty

  fun classify_primitive context ty =
    let
      fun suspend raw = if is_lazy context then MLSusp raw else raw
      fun algebraic strict = if is_lazy context then NONE else SOME strict
    in
      if Type.is_vartype ty then
        SOME (suspend (MLVar (clean_name (Type.dest_vartype ty))))
      else if Util.same_type ty Type.bool then SOME (suspend MLBool)
      else if Util.same_type ty numSyntax.num then SOME (suspend MLIntInf)
      else if Util.same_type ty intSyntax.int_ty then SOME (suspend MLIntInf)
      else if Util.same_type ty stringSyntax.char_ty then
        SOME (suspend MLChar)
      else if is_char_list ty andalso not (is_lazy context) then
        SOME MLString
      else if Util.same_type ty oneSyntax.one_ty then SOME (suspend MLUnit)
      else if wordsSyntax.is_word_type ty then
        SOME (suspend (MLWord (word_width ty)))
      else
        case Lib.total Type.dom_rng ty of
          SOME (domain, range) =>
            SOME (suspend (MLArrow (ensure_type context domain,
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
                val mlty = if is_lazy context then
                  MLSusp (MLDatatype ml_name) else MLDatatype ml_name
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
     if List.exists (Util.same_type ty) (!equalities) then ()
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
        if List.exists (Util.same_type ty) seen then false
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
      fun nonenumerable () =
        reject ("function equality has non-enumerable domain " ^ type_name ty)
      fun delayed value =
        if is_lazy context then
          "Susp.delay (fn () => " ^ value ^ ")"
        else value
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
                  enum_expression context argument ^ ")"
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
      else if is_lazy context then algebraic ()
      else
        case Lib.total optionSyntax.dest_option ty of
          SOME element =>
            "NONE :: List.map SOME " ^ parens (enum_expression context element)
        | NONE =>
            (case Lib.total pairSyntax.dest_prod ty of
               SOME (left, right) =>
                 "List.concat (List.map (fn a => List.map (fn b => " ^
                 "(a, b)) " ^ parens (enum_expression context right) ^
                 ") " ^ parens (enum_expression context left) ^ ")"
             | NONE => algebraic ())
    end

  fun equality_body context ty left right =
    let
      val represented = ensure_type context ty
      val mlty = case represented of MLSusp raw => raw | raw => raw
      fun force value = if is_lazy context then
        "Susp.force " ^ parens value else value
      val left_value = force left
      val right_value = force right
    in
      case mlty of
        MLBool =>
          parens ("(" ^ left_value ^ " andalso " ^ right_value ^
                  ") orelse (not " ^ left_value ^ " andalso not " ^
                  right_value ^ ")")
      | MLIntInf =>
          "IntInf.compare (" ^ left_value ^ ", " ^ right_value ^
          ") = EQUAL"
      | MLChar =>
          "Char.compare (" ^ left_value ^ ", " ^ right_value ^ ") = EQUAL"
      | MLString =>
          "String.compare (" ^ left_value ^ ", " ^ right_value ^
          ") = EQUAL"
      | MLUnit =>
          if is_lazy context then
            "let val _ = " ^ left_value ^ " val _ = " ^ right_value ^
            " in true end"
          else "true"
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
      | MLList _ =>
          let
            val element = listSyntax.dest_list_type ty
            val eq_element = equality_name context element
          in
            "let fun loop [] [] = true | loop (a :: as') (b :: bs') = " ^
            eq_element ^ " a b andalso loop as' bs' | loop _ _ = false " ^
            "in loop " ^ left_value ^ " " ^ right_value ^ " end"
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
            val (left_fun, right_fun) =
              if is_lazy context then ("left_fun", "right_fun")
              else (left, right)
            val body =
              "List.all (fn z => " ^ eq_range ^ " (" ^ left_fun ^
              " z) (" ^ right_fun ^ " z)) " ^
              parens (enum_expression context domain_ty)
          in
            if is_lazy context then
              "let val left_fun = " ^ left_value ^
              " val right_fun = " ^ right_value ^ " in " ^ body ^ " end"
            else body
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
      fun force value = if is_lazy context then
        "Susp.force " ^ parens value else value
    in
      "(case (" ^ force left ^ ", " ^ force right ^ ") of " ^
      join " | " (List.map clause (#constructors info)) ^
      " | _ => false)"
    end

  fun equality_declarations context =
    let
      fun discover seen =
        case List.find (fn ty =>
          not (List.exists (Util.same_type ty) seen))
          (!(#equalities context)) of
            NONE => ()
          | SOME ty =>
              (ignore (equality_body context ty "x" "y");
               discover (ty :: seen))
      val _ = if is_lazy context then discover [] else ()
      val requested = !(#equalities context)
      val types =
        if is_lazy context then
          List.filter (fn (ty, _, _) =>
            List.exists (Util.same_type ty) requested)
            (rev (!(#types context)))
        else rev (!(#types context))
      fun one keyword (ty, mlty, name) =
        keyword ^ " " ^ name ^ " (x : " ^ ml_ty_text mlty ^ ") " ^
        "(y : " ^ ml_ty_text mlty ^ ") =\n  " ^
        equality_body context ty "x" "y"
    in
      case types of
        [] => ""
      | first :: rest =>
          join "\n" (one "fun" first :: List.map (one "and") rest) ^ "\n"
    end

  val prelude =
    "fun refute_num_sub a b = if a < b then 0 else a - b\n" ^
    "fun refute_nonzero who b =\n" ^
    "  if b = 0 then raise Refute_EvalSML.Stuck who else b\n" ^
    "fun refute_num_div a b = IntInf.div (a, refute_nonzero \"DIV 0\" b)\n" ^
    "fun refute_num_mod a b = IntInf.mod (a, refute_nonzero \"MOD 0\" b)\n" ^
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
    "fun refute_tl [] = raise Refute_EvalSML.Stuck \"TL []\"\n" ^
    "  | refute_tl (_ :: xs) = xs\n" ^
    "fun refute_the NONE = raise Refute_EvalSML.Stuck \"THE NONE\"\n" ^
    "  | refute_the (SOME x) = x\n" ^
    "fun refute_chr n =\n" ^
    "  if n < 0 orelse n >= 256 then\n" ^
    "    raise Refute_EvalSML.Stuck \"CHR out of range\"\n" ^
    "  else Char.chr (IntInf.toInt n)\n" ^
    "fun refute_nth xs n =\n" ^
    "  (List.nth (xs, IntInf.toInt n)\n" ^
    "   handle _ => raise Refute_EvalSML.Stuck \"EL\")\n" ^
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
    "  refute_norm width\n" ^
    "    (refute_int_quot (refute_signed width a)\n" ^
    "      (refute_signed width b))\n" ^
    "fun refute_word_rem width a b =\n" ^
    "  refute_norm width\n" ^
    "    (refute_int_rem (refute_signed width a)\n" ^
    "      (refute_signed width b))\n" ^
    "fun refute_shift amount =\n" ^
    "  (Word.fromInt (IntInf.toInt amount)\n" ^
    "   handle _ => raise Refute_EvalSML.Stuck \"word shift\")\n" ^
    "fun refute_word_lsl width value amount =\n" ^
    "  refute_norm width (IntInf.<< (value, refute_shift amount))\n" ^
    "fun refute_word_lsr width value amount =\n" ^
    "  IntInf.~>> (refute_norm width value, refute_shift amount)\n" ^
    "fun refute_word_asr width value amount =\n" ^
    "  refute_norm width\n" ^
    "    (IntInf.~>> (refute_signed width value, refute_shift amount))\n" ^
    "fun refute_last [] = raise Refute_EvalSML.Stuck \"LAST []\"\n" ^
    "  | refute_last [x] = x\n" ^
    "  | refute_last (_ :: xs) = refute_last xs\n" ^
    "fun refute_front [] = raise Refute_EvalSML.Stuck \"FRONT []\"\n" ^
    "  | refute_front [_] = []\n" ^
    "  | refute_front (x :: xs) = x :: refute_front xs\n"

  fun lookup_definition ({definitions, ...} : context) constant =
    List.find (fn (other, _, _) => same_term other constant) (!definitions)

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
          val listing = computeLib.listItems (!computeLib.the_compset)
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
      SOME (_, name, _) => name
    | NONE =>
        if lookup_pending context constant then
          let val (_, name) = kname constant
          in
            case List.find (fn (other, _, _) =>
              Term.same_const other constant)
              (!(#definitions context)) of
              SOME (_, mlname, _) => mlname
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
                    val item = (member, fresh_const context base,
                                definition_theorem context member)
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
              SOME (_, name, _) => name
            | NONE =>
                reject ("mutual definition group omitted " ^
                        kname_text (kname constant))
          end

  fun variable_name variable = clean_name (#1 (Term.dest_var variable))

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
      val abstraction = List.foldr (fn (variable, result) =>
        "fn " ^ variable ^ " => " ^ result) body variables
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
  fun lazy_delay body = "Susp.delay (fn () => " ^ body ^ ")"
  fun lazy_force value = "Susp.force " ^ parens value
  fun lazy_defer value = lazy_delay (lazy_force value)

  fun lazy_apply function argument =
    lazy_defer (parens (lazy_force function ^ " " ^ parens argument))

  fun constructor_expression context constructor arguments =
    let
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
                lazy_delay ("fn " ^ variable ^ " => " ^
                  abstract variables body)
          val supplied = Int.min (length arguments, arity)
          val initial = List.take (arguments, supplied)
          val extra = List.drop (arguments, supplied)
          val variables = List.tabulate (arity - supplied, fn index =>
            "refute_arg_" ^ Int.toString index)
          val built = lazy_delay (custom name (initial @ variables))
          val abstraction = abstract variables built
        in
          List.foldl (fn (argument, result) =>
            lazy_apply result argument) abstraction extra
        end
      fun build_custom name =
        if is_lazy context then lazy_custom name
        else with_arity arguments arity (custom name)
    in
      if is_lazy context then
        (case constructor_for context constructor of
           SOME (_, _, name) => build_custom name
         | NONE => reject ("unknown lazy constructor " ^
                           kname_text (kname constructor)))
      else case kname constructor of
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
             SOME (_, _, name) => build_custom name
           | NONE => reject ("unknown constructor " ^
                             kname_text (kname constructor)))
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
          if is_lazy context then
            (case constructor_for context head of
               SOME (_, _, name) =>
                 (case List.map (pattern context) arguments of
                    [] => name
                  | [argument] => name ^ " " ^ argument
                  | values => name ^ " (" ^ join ", " values ^ ")")
             | NONE => reject ("unknown lazy pattern constructor " ^
                               kname_text (kname head)))
          else constructor_expression context head
            (List.map (pattern context) arguments)
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
          case values of [f, g, x] => parens (f ^ " " ^ parens
            (g ^ " " ^ parens x)) | _ => raise Fail "o"))
      | ("combin", "UPDATE") =>
          let
            val domain = hd (#1 (boolSyntax.strip_fun
              (Term.type_of head)))
            val equality = equality_name context domain
          in
            SOME (with_arity arguments 3 (fn values =>
              case values of [point, value, base] =>
                parens ("fn refute_update_x => if " ^ equality ^
                  " refute_update_x " ^ point ^ " then " ^ value ^
                  " else " ^ base ^ " refute_update_x")
              | _ => raise Fail "UPDATE"))
          end
      | ("pair", "FST") => SOME (call "#1" 1 arguments)
      | ("pair", "SND") => SOME (call "#2" 1 arguments)
      | ("pair", "CURRY") => SOME (with_arity arguments 3 (fn values =>
          case values of [f, a, b] => f ^ " " ^ parens (a ^ ", " ^ b)
          | _ => raise Fail "CURRY"))
      | ("pair", "UNCURRY") => SOME (with_arity arguments 2 (fn values =>
          case values of [f, pair] => f ^ " " ^ parens pair
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
              "else String.sub (" ^ a ^ ", 0)")
            else "refute_hd " ^ parens a
          | _ => raise Fail "HD"))
      | ("list", "TL") => SOME (with_arity arguments 1 (fn values =>
          case values of [a] =>
            if string_list () then parens ("if String.size " ^ parens a ^
              " = 0 then raise Refute_EvalSML.Stuck \"TL []\" " ^
              "else String.extract (" ^ a ^ ", 1, NONE)")
            else "refute_tl " ^ parens a
          | _ => raise Fail "TL"))
      | ("list", "APPEND") =>
          SOME (binary (if string_list () then "^" else "@") arguments)
      | ("list", "FLAT") => SOME (call "List.concat" 1 arguments)
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
      | ("list", "FOLDR") => SOME (call "refute_foldr" 3 arguments)
      | ("list", "FOLDL") => SOME (call "refute_foldl" 3 arguments)
      | ("list", "REVERSE") =>
          SOME (call (if string_list () then
            "(String.implode o List.rev o String.explode)" else "List.rev")
            1 arguments)
      | ("list", "EL") => SOME (with_arity arguments 2 (fn values =>
          case values of [n, xs] =>
            if string_argument 1 then
              "(String.sub (" ^ xs ^ ", IntInf.toInt " ^ n ^ ") " ^
              "handle _ => raise Refute_EvalSML.Stuck \"EL\")"
            else "refute_nth " ^ xs ^ " " ^ n
          | _ => raise Fail "EL"))
      | ("list", "LAST") => SOME (call "refute_last" 1 arguments)
      | ("list", "FRONT") => SOME (call "refute_front" 1 arguments)
      | ("list", "SNOC") => SOME (with_arity arguments 2 (fn values =>
          case values of [x, xs] => xs ^ " @ [" ^ x ^ "]"
          | _ => raise Fail "SNOC"))
      | ("list", "ALL_DISTINCT") =>
          SOME (call ("refute_all_distinct " ^ list_eq_argument ())
            1 arguments)
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
              parens value ^ " = 0 then NONE else SOME (String.sub (" ^
              value ^ ", 0), String.extract (" ^ value ^ ", 1, NONE))")
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
              " (refute_pow " ^ a ^ " " ^ b ^ ")"
            | _ => raise Fail "word_exp")) end
      | ("words", "word_1comp") =>
          let val width = word_result_width head argument_terms
          in SOME (with_arity arguments 1 (fn values =>
            case values of [a] => "refute_norm " ^ Int.toString width ^
              " (IntInf.notb " ^ a ^ ")"
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
              Int.toString width ^ " " ^ value ^ " < 0"
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
                Int.toString input_width ^ " " ^ value ^ ")"
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

  fun lazy_with_arity arguments arity build =
    let
      val supplied = Int.min (length arguments, arity)
      val initial = List.take (arguments, supplied)
      val extra = List.drop (arguments, supplied)
      val variables = List.tabulate (arity - supplied, fn index =>
        "refute_lazy_arg_" ^ Int.toString index)
      val body = build (initial @ variables)
      val abstraction = List.foldr (fn (variable, result) =>
        "Susp.delay (fn () => fn " ^ variable ^ " => " ^ result ^ ")")
        body variables
    in
      List.foldl (fn (argument, result) =>
        lazy_apply result argument) abstraction extra
    end

  fun lazy_primitive context head argument_terms arguments =
    let
      val key = kname head
      val arity = length (#1 (boolSyntax.strip_fun (Term.type_of head)))
      val delay = lazy_delay
      val force = lazy_force
      fun unary operation = lazy_with_arity arguments 1 (fn values =>
        case values of [value] => delay (operation (force value))
        | _ => raise Fail "lazy unary")
      fun binary operation = lazy_with_arity arguments 2 (fn values =>
        case values of [left, right] =>
          delay (operation (force left, force right))
        | _ => raise Fail "lazy binary")
      fun flat () = lazy_with_arity arguments arity (fn values =>
        let
          val forced = map force values
          val source = strict_primitive context head argument_terms forced
        in
          case source of
              SOME body => delay body
            | NONE => reject ("unsupported lazy primitive " ^
                              kname_text key)
        end)
      fun pair_selector index = lazy_with_arity arguments 1 (fn values =>
        case values of
            [value] =>
              let
                val ty = #1 (Type.dom_rng (Term.type_of head))
                val info = valOf (lookup_datatype context ty)
                val (_, _, constructor) = hd (#constructors info)
                val fields = if index = 0 then "left" else "right"
              in
                lazy_defer
                  (parens ("case " ^ force value ^ " of " ^ constructor ^
                    " (left, right) => " ^ fields))
              end
          | _ => raise Fail "lazy pair selector")
      fun list_case value nil_body cons_body =
        let
          val ty = #1 (Type.dom_rng (Term.type_of head))
          val info = valOf (lookup_datatype context ty)
          fun named name = valOf (List.find (fn (constructor, _, _) =>
            kname constructor = ("list", name)) (#constructors info))
          val (_, _, nil_name) = named "NIL"
          val (_, _, cons_name) = named "CONS"
        in
          "(case " ^ force value ^ " of " ^ nil_name ^ " => " ^ nil_body ^
          " | " ^ cons_name ^ " (refute_head, refute_tail) => " ^ cons_body ^
          ")"
        end
    in
      case key of
          ("bool", "T") => SOME (delay "true")
        | ("bool", "F") => SOME (delay "false")
        | ("bool", "ARB") => SOME
            (delay "(raise Refute_EvalSML.Stuck \"ARB\")")
        | ("bool", "~") => SOME (unary (fn value => "not " ^ value))
        | ("bool", "/\\") => SOME (binary (fn (left, right) =>
            left ^ " andalso " ^ right))
        | ("bool", "\\/") => SOME (binary (fn (left, right) =>
            left ^ " orelse " ^ right))
        | ("min", "==>") => SOME (binary (fn (left, right) =>
            "not " ^ parens left ^ " orelse " ^ right))
        | ("min", "=") =>
            let val compared = #1 (Type.dom_rng (Term.type_of head))
            in
              SOME (lazy_with_arity arguments 2 (fn values =>
                case values of [left, right] =>
                  delay (equality_name context compared ^ " " ^
                    parens left ^ " " ^ parens right)
                | _ => raise Fail "lazy equality"))
            end
        | ("combin", "I") => SOME (lazy_with_arity arguments 1 (fn values =>
            case values of [value] => lazy_defer value
            | _ => raise Fail "lazy I"))
        | ("combin", "K") => SOME (lazy_with_arity arguments 2 (fn values =>
            case values of [value, _] => lazy_defer value
            | _ => raise Fail "lazy K"))
        | ("combin", "o") => SOME (lazy_with_arity arguments 3 (fn values =>
            case values of [f, g, x] => lazy_apply f (lazy_apply g x)
            | _ => raise Fail "lazy composition"))
        | ("pair", "FST") => SOME (pair_selector 0)
        | ("pair", "SND") => SOME (pair_selector 1)
        | ("list", "NULL") => SOME (lazy_with_arity arguments 1 (fn values =>
            case values of [value] => delay (list_case value "true" "false")
            | _ => raise Fail "lazy NULL"))
        | ("list", "HD") => SOME (lazy_with_arity arguments 1 (fn values =>
            case values of [value] => lazy_defer (list_case value
              "(raise Refute_EvalSML.Stuck \"HD []\")" "refute_head")
            | _ => raise Fail "lazy HD"))
        | ("list", "TL") => SOME (lazy_with_arity arguments 1 (fn values =>
            case values of [value] => lazy_defer (list_case value
              "(raise Refute_EvalSML.Stuck \"TL []\")" "refute_tail")
            | _ => raise Fail "lazy TL"))
        | ("option", "THE") =>
            let
              fun build values =
                case values of
                    [value] =>
                      let
                        val ty = #1 (Type.dom_rng (Term.type_of head))
                        val info = valOf (lookup_datatype context ty)
                        fun named name = #3 (valOf (List.find
                          (fn (constructor, _, _) =>
                            kname constructor = ("option", name))
                          (#constructors info)))
                      in
                        lazy_defer
                          ("(case " ^ force value ^ " of " ^ named "NONE" ^
                           " => raise Refute_EvalSML.Stuck \"THE NONE\" | " ^
                           named "SOME" ^ " result => result)")
                      end
                  | _ => raise Fail "lazy THE"
            in SOME (lazy_with_arity arguments 1 build) end
        | (thy, _) =>
            if Lib.mem thy
              ["num", "arithmetic", "prim_rec", "integer", "words",
               "integer_word"]
            then SOME (flat ())
            else NONE
    end

  fun primitive context head argument_terms arguments =
    if is_lazy context then
      lazy_primitive context head argument_terms arguments
    else strict_primitive context head argument_terms arguments

  fun expression context term =
    if is_lazy context then lazy_expression context term
    else strict_expression context term

  and strict_expression context term =
    if Term.is_var term then variable_name term
    else if boolSyntax.is_cond term then
      let val (condition, left, right) = boolSyntax.dest_cond term
      in
        parens ("if " ^ expression context condition ^ " then " ^
          expression context left ^ " else " ^ expression context right)
      end
    else if boolSyntax.is_let term then
      let
        val (groups, body) = pairSyntax.strip_anylet term
        fun binding (left, right) =
          "val " ^ pattern context left ^ " = " ^ expression context right
        fun group bindings = join "\n" (List.map binding bindings)
      in
        parens ("let\n" ^ join "\n" (List.map group groups) ^ "\nin " ^
                expression context body ^ "\nend")
      end
    else if Literal.is_numeral term then
      num_literal (Literal.relaxed_dest_numeral term)
    else if intSyntax.is_int_literal term then
      int_literal (intSyntax.int_of_term term)
    else if Literal.is_char_lit term then
      "#" ^ quote (String.str (Literal.dest_char_lit term))
    else if Literal.is_string_lit term then
      quote (Literal.relaxed_dest_string_lit term)
    else if wordsSyntax.is_word_literal term then
      num_literal (wordsSyntax.dest_word_literal term)
    else if pairSyntax.is_pair term then
      let val (left, right) = pairSyntax.dest_pair term
      in parens (expression context left ^ ", " ^ expression context right)
      end
    else if listSyntax.is_list term andalso not (is_char_list
      (Term.type_of term)) then
      let val (elements, _) = listSyntax.dest_list term
      in "[" ^ join ", " (List.map (expression context) elements) ^ "]" end
    else if pairSyntax.is_pabs term then
      let val (argument, body) = pairSyntax.dest_pabs term
      in parens ("fn " ^ pattern context argument ^ " => " ^
                 expression context body)
      end
    else if Term.is_abs term then
      let val (argument, body) = Term.dest_abs term
      in parens ("fn " ^ variable_name argument ^ " => " ^
                 expression context body)
      end
    else if oneSyntax.is_one term then "()"
    else if TypeBase.is_record term then
      let
        val (record_ty, fields) = TypeBase.dest_record term
        val constructor = hd (TypeBase.constructors_of record_ty)
      in
        constructor_expression context constructor
          (List.map (expression context o #2) fields)
      end
    else if TypeBase.is_case term then
      let
        val (scrutinee, rows) = TypeBase.strip_case term
        fun row (pat, rhs) = pattern context pat ^ " => " ^
          expression context rhs
        fun string_rows () =
          let
            fun classify (pat, rhs) =
              let val (head, arguments) = boolSyntax.strip_comb pat
              in
                case kname head of
                  ("list", "NIL") => SOME (true, arguments, rhs)
                | ("list", "CONS") => SOME (false, arguments, rhs)
                | _ => NONE
              end
            val classified = List.mapPartial classify rows
            val nil_row = List.find #1 classified
            val cons_row = List.find (not o #1) classified
          in
            case (nil_row, cons_row) of
              (SOME (_, _, nil_rhs), SOME (_, variables, cons_rhs)) =>
                (case variables of
                   [head, tail] =>
                     parens ("if String.size " ^
                       parens (expression context scrutinee) ^
                       " = 0 then " ^ expression context nil_rhs ^
                       " else let val " ^ pattern context head ^
                       " = String.sub (" ^ expression context scrutinee ^
                       ", 0) val " ^ pattern context tail ^
                       " = String.extract (" ^
                       expression context scrutinee ^
                       ", 1, NONE) in " ^ expression context cons_rhs ^
                       " end")
                 | _ => reject "malformed string case")
            | _ => reject "malformed string case"
          end
      in
        if is_char_list (Term.type_of scrutinee) then string_rows ()
        else parens ("case " ^ expression context scrutinee ^ " of " ^
          join " | " (List.map row rows))
      end
    else
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
                   val (domains, _) = boolSyntax.strip_fun (Term.type_of head)
                   val base = if null domains then name ^ " ()" else name
                 in
                   List.foldl (fn (argument, result) =>
                     parens (result ^ " " ^ parens argument)) base arguments
                 end)
        else
          List.foldl (fn (argument, result) =>
            parens (result ^ " " ^ parens argument))
            (expression context head) arguments
      end

  and lazy_expression context term =
    let
      val delay = lazy_delay
      val force = lazy_force
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
      fun application head arguments =
        List.foldl (fn (argument, result) =>
          lazy_apply result argument) head arguments
    in
      if Term.is_var term then variable_name term
      else if boolSyntax.is_cond term then
        let val (condition, left, right) = boolSyntax.dest_cond term
        in
          lazy_defer
            (parens ("if " ^ force (expression context condition) ^
              " then " ^ expression context left ^ " else " ^
              expression context right))
        end
      else if boolSyntax.is_let term then
        let
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
          lazy_defer (compile_groups groups)
        end
      else if Literal.is_numeral term then
        delay (num_literal (Literal.relaxed_dest_numeral term))
      else if intSyntax.is_int_literal term then
        delay (int_literal (intSyntax.int_of_term term))
      else if Literal.is_char_lit term then
        delay ("#" ^ quote (String.str (Literal.dest_char_lit term)))
      else if Literal.is_string_lit term then
        let
          val chars = List.map (fn character =>
            delay ("#" ^ quote (String.str character)))
            (String.explode (Literal.relaxed_dest_string_lit term))
        in
          list_value stringSyntax.string_ty chars
        end
      else if wordsSyntax.is_word_literal term then
        delay (num_literal (wordsSyntax.dest_word_literal term))
      else if pairSyntax.is_pair term then
        let
          val (left, right) = pairSyntax.dest_pair term
          val ty = Term.type_of term
          val constructor = TypeBasePure.cinst ty
            (hd (TypeBase.constructors_of ty))
        in
          constructor_expression context constructor
            [expression context left, expression context right]
        end
      else if listSyntax.is_list term then
        let val (elements, ty) = listSyntax.dest_list term
        in list_value (Term.type_of term)
          (List.map (expression context) elements) end
      else if pairSyntax.is_pabs term then
        let
          val (argument, body) = pairSyntax.dest_pabs term
          val argument_name = fresh_pattern context
            "refute_lazy_pair_argument_"
          val matched = lazy_match_pattern context argument argument_name
            (expression context body) "(raise Match)"
        in
          delay ("fn " ^ argument_name ^ " => " ^ matched)
        end
      else if Term.is_abs term then
        let val (argument, body) = Term.dest_abs term
        in
          delay ("fn " ^ variable_name argument ^ " => " ^
            expression context body)
        end
      else if oneSyntax.is_one term then delay "()"
      else if TypeBase.is_record term then
        let
          val (record_ty, fields) = TypeBase.dest_record term
          val constructor = hd (TypeBase.constructors_of record_ty)
        in
          constructor_expression context constructor
            (List.map (expression context o #2) fields)
        end
      else if TypeBase.is_case term then
        let
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
          lazy_defer
            (parens ("let val " ^ value ^ " = " ^
              expression context scrutinee ^ "\nin " ^ dispatch rows ^
              "\nend"))
        end
      else
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
                     val (domains, _) =
                       boolSyntax.strip_fun (Term.type_of head)
                     fun invoke values = lazy_defer
                       (if null values then name ^ " ()"
                        else name ^ " " ^
                          join " " (List.map parens values))
                   in
                     lazy_with_arity arguments (length domains) invoke
                   end)
          else application (expression context head) arguments
        end
    end

  (* Match one HOL pattern against a suspended value.  Constructor spines and
     literals are observations, so they force the suspension being tested.
     Constructor fields remain suspended: variable and wildcard fields are
     bound or skipped as-is, while nested tests observe fields left-to-right.
     Keeping failure explicit also lets case rows and definition clauses share
     this compiler without relying on eager SML patterns. *)
  and lazy_match_pattern context tm value success failure =
    if Term.is_var tm then
      let val variable = variable_name tm
      in
        if variable = "_" then success
        else "let val " ^ variable ^ " = " ^ value ^ " in " ^
          success ^ " end"
      end
    else if Literal.is_numeral tm orelse intSyntax.is_int_literal tm orelse
            Literal.is_char_lit tm orelse Literal.is_string_lit tm orelse
            oneSyntax.is_one tm orelse Term.aconv tm boolSyntax.T orelse
            Term.aconv tm boolSyntax.F orelse
            wordsSyntax.is_word_literal tm then
      "if " ^ equality_name context (Term.type_of tm) ^ " " ^
        parens value ^ " " ^ parens (expression context tm) ^ " then " ^
        success ^ " else " ^ failure
    else
      let
        val (head, arguments) = boolSyntax.strip_comb tm
      in
        if Term.is_const head andalso kname head = ("num", "SUC") then
          (case arguments of
               [argument] =>
                 let
                   val raw = fresh_pattern context "refute_lazy_suc_"
                   val predecessor = lazy_delay (parens (raw ^ " - 1"))
                 in
                   "let val " ^ raw ^ " = " ^ lazy_force value ^ " in " ^
                   "if " ^ raw ^ " > 0 then " ^
                   lazy_match_pattern context argument predecessor success
                     failure ^ " else " ^ failure ^ " end"
                 end
             | _ => reject "malformed lazy SUC pattern")
        else if Term.is_const head andalso TypeBase.is_constructor head then
          let
            val (_, _, constructor) =
              case constructor_for context head of
                  SOME found => found
                | NONE => reject ("unknown lazy pattern constructor " ^
                                  kname_text (kname head))
            val children = List.map (fn _ =>
              fresh_pattern context "refute_lazy_field_") arguments
            fun payload [] = constructor
              | payload [child] = constructor ^ " " ^ child
              | payload fields = constructor ^ " (" ^
                  join ", " fields ^ ")"
            val body = List.foldr
              (fn ((argument, child), rest) =>
                lazy_match_pattern context argument child rest failure)
              success (ListPair.zip (arguments, children))
          in
            parens ("case " ^ lazy_force value ^ " of " ^
              payload children ^ " => " ^ body ^ " | _ => " ^
              failure)
          end
        else
          reject ("unsupported lazy pattern: " ^
                  Parse.term_to_string tm)
      end

  fun strict_definition_clause context (constant, name, theorem) =
    let
      val next_pattern = ref 0
      fun fresh_pattern () =
        let val number = !next_pattern
            val _ = next_pattern := number + 1
        in "refute_pattern_" ^ Int.toString number end
      fun strip_suc count tm =
        let val (head, arguments) = boolSyntax.strip_comb tm
        in
          if Term.is_const head andalso kname head = ("num", "SUC") then
            case arguments of
              [argument] => strip_suc (count + 1) argument
            | _ => reject "malformed SUC pattern"
          else
            (count, tm)
        end
      fun compiled_pattern tm =
        let val (successors, base) = strip_suc 0 tm
        in
          if successors = 0 then (pattern context tm, [], [])
          else
            let
              val variable = fresh_pattern ()
              val predecessor = parens (variable ^ " - " ^
                Int.toString successors)
              val lower_bound = variable ^ " >= " ^
                Int.toString successors
            in
              if Term.is_var base then
                let val base_name = variable_name base
                    val bindings = if base_name = "_" then [] else
                      ["val " ^ base_name ^ " = " ^ predecessor]
                in (variable, [lower_bound], bindings) end
              else if Literal.is_numeral base then
                let val number = Literal.relaxed_dest_numeral base
                in
                  (variable,
                   [lower_bound, predecessor ^ " = " ^
                    Arbnum.toString number], [])
                end
              else
                reject ("unsupported successor pattern: " ^
                        Parse.term_to_string tm)
            end
        end
      fun equation_info equation =
        let
          val (left, right) = boolSyntax.dest_eq equation
            handle Feedback.HOL_ERR _ =>
              reject ("non-equational rule for " ^
                      kname_text (kname constant))
          val (head, arguments) = boolSyntax.strip_comb left
          val _ =
            if Term.is_const head andalso Term.same_const head constant then ()
            else reject ("rule has the wrong head for " ^
                         kname_text (kname constant))
          val patterns = List.map compiled_pattern arguments
        in
          { patterns = List.map #1 patterns,
            guards = List.concat (List.map #2 patterns),
            bindings = List.concat (List.map #3 patterns),
            rhs = expression context right }
        end
      val equations = equations_of theorem
      val infos = List.map equation_info equations
      val _ =
        if null infos then reject ("definition has no clauses for " ^
          kname_text (kname constant)) else ()
      val arity = length (#patterns (hd infos))
      val _ =
        if List.all (fn info => length (#patterns info) = arity) infos then ()
        else reject ("definition has inconsistent arities for " ^
                     kname_text (kname constant))
      val arguments = List.tabulate (arity, fn index =>
        "refute_argument_" ^ Int.toString index)
      fun tuple [] = "()"
        | tuple [item] = item
        | tuple items = parens (join ", " items)
      fun guarded {guards, bindings, rhs, ...} fallback =
        let
          val body = if null bindings then rhs else
            parens ("let " ^ join " " bindings ^ " in " ^ rhs ^ " end")
        in
          if null guards then body
          else parens ("if " ^ join " andalso " guards ^ " then " ^
                       body ^ " else " ^ fallback)
        end
      fun dispatch [] = "(raise Match)"
        | dispatch (info :: rest) =
            let
              val fallback = "refute_next ()"
              val next = dispatch rest
            in
              parens ("let fun refute_next () = " ^ next ^ " in case " ^
                tuple arguments ^ " of " ^ tuple (#patterns info) ^
                " => " ^ guarded info fallback ^ " | _ => " ^
                fallback ^ " end")
            end
      val lhs = if null arguments then name ^ " ()"
                else name ^ " " ^ join " " arguments
    in
      lhs ^ " = " ^ dispatch infos
    end

  fun lazy_definition_clause context (constant, name, theorem) =
    let
      fun equation equation =
        let
          val (left, right) = boolSyntax.dest_eq equation
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
      val arguments = List.tabulate (arity, fn index =>
        "refute_argument_" ^ Int.toString index)
      fun dispatch [] = "(raise Match)"
        | dispatch ((patterns, rhs) :: rest) =
            let
              val fallback = "refute_next ()"
              val body = List.foldr
                (fn ((pat, argument), success) =>
                  lazy_match_pattern context pat argument success fallback)
                (expression context rhs)
                (ListPair.zip (patterns, arguments))
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
    if is_lazy context then lazy_definition_clause context item
    else strict_definition_clause context item

  (* Compiling a clause is the expensive part of extraction and its text
     is final once produced (names are fixed at registration), so the
     drain pass and the declarations pass share one compilation. *)
  fun cached_definition_clause context (item as (constant, _, _)) =
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

  fun drain_definitions context =
    let
      fun loop processed =
        case List.find (fn (constant, _, _) =>
          not (List.exists (same_term constant) processed))
          (rev (!(#definitions context))) of
          NONE => ()
        | SOME (item as (constant, _, _)) =>
            (ignore (cached_definition_clause context item);
             loop (constant :: processed))
    in
      loop []
    end

  fun definition_declarations context =
    let
      val definitions = rev (!(#definitions context))
      val groups = rev (!(#definition_groups context))
      fun item_for constant =
        case List.find (fn (other, _, _) => same_term other constant)
          definitions of
          SOME item => item
        | NONE => raise Fail "Refute_Extract: missing definition"
      fun group_for constant =
        List.find (List.exists (same_term constant)) groups
      fun constants_in (_, _, theorem) =
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
    (if is_lazy context then
       "fun refute_hole position = Refute_EvalSML.lazy_hole position\n\n"
     else "") ^
    String.concat (List.map (datatype_declaration context)
      (datatype_groups context)) ^ "\n" ^
    equality_declarations context ^ "\n"

  fun compile_types_with mode types =
    let
      val context = new_context mode
      val mltypes = List.map (ensure_type context) types
      val _ = List.app (fn ty => ignore (equality_name context ty)) types
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
  fun compile_lazy_types types = compile_types_with Lazy types
  fun compile_lazy_type ty = compile_lazy_types [ty]

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

  fun extract_tests_with mode strict
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
        | SmartGuard {predicate, version, cont} =>
            SmartGuard
              {predicate = substitute_variables environment predicate,
               version = version, cont = rename_plan cont environment}
        | Enum {rel, mode, version, ins, outs, cont} =>
            let
              val bound = map #1 environment
              val output_variables = List.foldl (fn (variable, result) =>
                if List.exists (fn old => Term.aconv old variable)
                     (bound @ result)
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

      (* TASK_14 installs only the lazy property compiler.  Generation and
         refinement belong to the narrowing engine; accepting those nodes
         here would accidentally run strict enumeration over lazy values. *)
      fun test_only current =
        case current of
            Test _ => true
          | Guard (_, next) => test_only next
          | Prune => true
          | _ => false
      val _ =
        if mode = Lazy andalso not (List.all test_only plans) then
          reject "native: narrowing engine is not installed"
        else ()

      fun same_program
            ({relation = left, mode = left_mode, version = left_version, ...} :
              Refute_SmartGen.enumerator)
            ({relation = right, mode = right_mode,
              version = right_version, ...} :
              Refute_SmartGen.enumerator) =
        Refute_SmartGen.same_relation left right andalso
        Refute_SmartGen.eq_mode (left_mode, right_mode) andalso
        Refute_SmartGen.same_program_version
          (left_version, right_version)

      fun add_program program programs =
        if List.exists (same_program program) programs then programs
        else programs @ [program]

      fun cached_all_input predicate expected_version =
        if not (#smart_generators (#qc config)) orelse
           strategy <> Exhaustive then NONE
        else
          let
            val (head, arguments) = HolKernel.strip_comb predicate
            fun find {program =
                  (program as {relation, mode, version, ...} :
                    Refute_SmartGen.enumerator), ...} =
              if Refute_SmartGen.same_relation head relation andalso
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

      fun program_closure current programs =
        let
          val programs = add_program current programs
          val {clauses, ...} = current
          fun called (Refute_SmartGen.CpsClause {premises, ...}) =
            List.mapPartial (fn Refute_SmartGen.CpsCall
                {rel, mode, ...} =>
                  (case Refute_SmartGen.enumerator_for_in
                       enum_cache rel mode of
                       SOME program => SOME program
                     | NONE => reject
                         "smart plan: missing recursive enumerator dependency")
              | _ => NONE) premises
          fun visit program result =
            if List.exists (same_program program) result then result
            else program_closure program result
        in
          List.foldl (fn (program, result) => visit program result)
            programs (List.concat (map called clauses))
        end

      fun collect_programs current programs =
        case current of
            Test _ => programs
          | Gen (_, next) => collect_programs next programs
          | Bind (_, _, fallback, next) =>
              collect_programs next
                (case fallback of NONE => programs
                 | SOME other => collect_programs other programs)
          | Split (_, branches) =>
              List.foldl (fn ((_, _, next), result) =>
                collect_programs next result) programs branches
          | Guard (_, next) => collect_programs next programs
          | SmartGuard {predicate, version, cont} =>
              let
                val program =
                  case cached_all_input predicate version of
                      SOME (found, _) => found
                    | NONE => reject
                        "smart plan: stale or non-all-input smart Guard"
              in
                collect_programs cont (program_closure program programs)
              end
          | Enum {rel, mode, version, cont, ...} =>
              let
                val program =
                  case Refute_SmartGen.enumerator_for_in
                    enum_cache rel mode of
                      SOME found =>
                        if Refute_SmartGen.same_program_version
                             (version, #version found)
                        then found
                        else reject "smart plan: stale Enum version"
                    | NONE => reject
                        "smart plan: missing top-level enumerator program"
              in
                collect_programs cont (program_closure program programs)
              end
          | Prune => programs

      val enum_programs = List.foldl (fn (plan, programs) =>
        collect_programs plan programs) [] plans

      fun smart_reject message = reject ("smart plan: " ^ message)

      fun same_type left right = Util.same_type left right
      fun same_types left right =
        length left = length right andalso
        ListPair.allEq (fn (first, second) => same_type first second)
          (left, right)
      fun vars_bound bound tm =
        List.all (fn variable => List.exists (fn old =>
          Term.aconv old variable) bound) (Term.free_vars_lr tm)
      fun require_bound label bound terms =
        if List.all (vars_bound bound) terms then ()
        else smart_reject (label ^ " uses an unbound variable")
      fun fresh_in bound variable =
        not (List.exists (fn old => Term.aconv old variable) bound)

      fun validate_executable label consumed terms =
        if not strict andalso null enum_programs then ()
        else
          let
            val constants = Refute_Core.nonexecutable_constants terms
            val remaining = List.filter (fn constant =>
              not (List.exists (fn allowed =>
                Term.same_const allowed constant) consumed)) constants
            val has_binder = List.exists (fn tm =>
              not (null (HolKernel.find_terms Term.is_abs tm))) terms
          in
            if has_binder then
              smart_reject (label ^ " contains an unexpanded binder")
            else if null remaining then ()
            else smart_reject (label ^ " is nonexecutable: " ^
              Refute_Core.show_constants remaining)
          end

      fun mode_shape relation mode =
        let
          val _ =
            if Term.is_const relation then ()
            else smart_reject "enumerator relation is not a constant"
          val (domains, range) = boolSyntax.strip_fun (Term.type_of relation)
          val _ =
            if same_type range Type.bool then ()
            else smart_reject "enumerator relation does not return bool"
          val modes = Refute_SmartGen.strip_mode mode
          val _ =
            if length domains = length modes andalso
               List.all Refute_SmartGen.first_order_mode modes then ()
            else smart_reject "enumerator mode/arity mismatch"
          val arguments = List.map (fn (index, ty) =>
            Term.mk_var ("refute_validate_" ^ Int.toString index, ty))
            (Lib.enumerate 0 domains)
          val (ins, outs) = Refute_SmartGen.split_arguments mode arguments
        in
          (map Term.type_of ins, map Term.type_of outs)
        end
        handle Feedback.HOL_ERR _ =>
          smart_reject "enumerator mode/type mismatch"

      fun program_for relation mode =
        case List.find (fn ({relation = other, mode = other_mode, ...} :
            Refute_SmartGen.enumerator) =>
          Refute_SmartGen.same_relation relation other andalso
          Refute_SmartGen.eq_mode (mode, other_mode)) enum_programs of
            SOME program => program
          | NONE => smart_reject "enumerator dependency is absent"

      fun validate_program
            ({relation, mode, clauses, ...} : Refute_SmartGen.enumerator) =
        let
          val (input_types, output_types) = mode_shape relation mode
          fun introduce bound terms =
            List.foldl (fn (variable, current) =>
              if fresh_in current variable then current @ [variable]
              else current) bound (List.concat (map Term.free_vars_lr terms))
          fun premise (premise, current) =
            case premise of
                Refute_SmartGen.CpsGenerate variable =>
                  if Term.is_var variable andalso fresh_in current variable
                  then current @ [variable]
                  else smart_reject
                    "generator variable is malformed or already bound"
              | Refute_SmartGen.CpsGuard tm =>
                  (require_bound "enumerator Guard" current [tm];
                   validate_executable "enumerator Guard" [] [tm]; current)
              | Refute_SmartGen.CpsCall {rel, mode, ins, outs} =>
                  let
                    val dependency = program_for rel mode
                    val _ = ignore dependency
                    val (expected_ins, expected_outs) = mode_shape rel mode
                    val _ =
                      if same_types (map Term.type_of ins) expected_ins andalso
                         same_types (map Term.type_of outs) expected_outs
                      then ()
                      else smart_reject
                        "recursive call mode/arity/types mismatch"
                    val _ = require_bound "recursive call input" current ins
                    val _ = validate_executable
                      "recursive call input" [] ins
                  in
                    introduce current outs
                  end
          fun clause (Refute_SmartGen.CpsClause
                {ins, premises, outs}) =
            let
              val _ =
                if same_types (map Term.type_of ins) input_types andalso
                   same_types (map Term.type_of outs) output_types then ()
                else smart_reject "clause mode/arity/types mismatch"
              val current = introduce [] ins
              val current = List.foldl premise current premises
              val _ = require_bound "clause output" current outs
            in
              ()
            end
        in
          List.app clause clauses
        end

      val _ = List.app validate_program enum_programs

      fun validate_plan current bound =
        case current of
            Test tm =>
              (require_bound "Test" bound [tm];
               validate_executable "Test" [] [tm])
          | Gen (variable, next) =>
              if Term.is_var variable andalso fresh_in bound variable then
                validate_plan next (variable :: bound)
              else smart_reject "Gen variable is malformed or already bound"
          | Bind (variable, tm, fallback, next) =>
              (require_bound "Bind expression" bound [tm];
               validate_executable "Bind expression" [] [tm];
               if Term.is_var variable andalso fresh_in bound variable then ()
               else smart_reject
                 "Bind variable is malformed or already bound";
               Option.app (fn other => validate_plan other bound) fallback;
               validate_plan next (variable :: bound))
          | Split (tm, branches) =>
              let
                val _ = require_bound "Split scrutinee" bound [tm]
                val _ = validate_executable "Split scrutinee" [] [tm]
                fun branch (_, variables, next) =
                  if List.all (fresh_in bound) variables then
                    validate_plan next (variables @ bound)
                  else smart_reject "Split branch variable is already bound"
              in
                List.app branch branches
              end
          | Guard (tm, next) =>
              (require_bound "Guard" bound [tm];
               validate_executable "Guard" [] [tm];
               validate_plan next bound)
          | SmartGuard {predicate, version, cont} =>
              let
                val (program as {relation, ...}, ins) =
                  case cached_all_input predicate version of
                      SOME found => found
                    | NONE => smart_reject
                        "stale or non-all-input smart Guard"
                val _ = ignore program
              in
                require_bound "smart Guard" bound [predicate];
                require_bound "smart Guard input" bound ins;
                validate_executable "smart Guard" [relation] [predicate];
                validate_plan cont bound
              end
          | Enum {rel, mode, version, ins, outs, cont} =>
              let
                val {relation, mode = program_mode,
                     version = program_version, ...} = program_for rel mode
                val _ =
                  if Refute_SmartGen.same_relation rel relation andalso
                     Refute_SmartGen.eq_mode (mode, program_mode) andalso
                     Refute_SmartGen.same_program_version
                       (version, program_version)
                  then ()
                  else smart_reject "stale enumerator cache key/version"
                val (expected_ins, expected_outs) = mode_shape rel mode
                val _ =
                  if same_types (map Term.type_of ins) expected_ins andalso
                     same_types (map Term.type_of outs) expected_outs then ()
                  else smart_reject "Enum mode/arity/types mismatch"
                val _ = require_bound "Enum input" bound ins
                val _ = validate_executable "Enum input" [] ins
                val introduced = List.foldl (fn (variable, result) =>
                  if fresh_in (bound @ result) variable then
                    result @ [variable] else result) []
                  (List.concat (map Term.free_vars_lr outs))
              in
                validate_plan cont (introduced @ bound)
              end
          | Prune => ()

      val _ = List.app (fn plan => validate_plan plan []) plans

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
                if List.exists (fn old => Term.aconv old variable) result
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
      fun integer value = Int.toString value
      fun intinf value =
        "(valOf (IntInf.fromString " ^ quote (IntInf.toString value) ^ ") " ^
        ": IntInf.int)"
      fun pair value thunk = parens (value ^ ", " ^ thunk)
      fun thunk body = "(fn () => " ^ body ^ ")"
      fun term_list items = "[" ^ join ", " items ^ "]"
      fun maximum values = List.foldl Int.max 0 values

      fun custom_type ty =
        Option.isSome (Refute_Gen.generator_of ty) orelse
        List.exists (fn (other, _) => Util.same_type other ty)
          (!(Refute_Gen.abstract_specs))

      val validated = ref ([] : hol_type list)

      fun validate_type root ty =
        if List.exists (Util.same_type ty) (!validated) then ()
        else
          let
            val _ = validated := ty :: !validated
            val _ =
              if custom_type ty then
                reject ("custom generator registered for " ^ type_name root)
              else ()
          in
            case Refute_Gen.spec_of ty of
              Refute_Gen.GenDatatype {constrs, ...} =>
                List.app (validate_type root)
                  (List.concat (List.map #2 constrs))
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
            if List.exists (Util.same_type ty) seen then close_types rest seen
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
            "refute_range 0 (IntInf.toInt (IntInf.min " ^
            "(IntInf.fromInt (Int.max (0, size)), " ^
            "IntInf.pow (2, " ^ integer width ^ ") - 1))) (fn n => " ^
            pair ("IntInf.fromInt n")
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
          val variable = Term.mk_var
            ("refute_function_argument", domain)
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

      fun random_arguments [] [] _ _ state continuation =
            continuation ([], state)
        | random_arguments (ty :: tys) (flag :: flags) budget size state
            continuation =
            let
              val number = length tys
              val generated = "generated_" ^ integer number
              val next = "state_" ^ integer number
              val call = if flag then generator_name "rnd_aux_" ty ^ " " ^
                "(Int.max (0, " ^ budget ^ " - 1)) " ^ size ^ " " ^ state
                else generator_name "rnd_" ty ^ " " ^ size ^ " " ^ state
            in
              "let val (" ^ generated ^ ", " ^ next ^ ") = " ^ call ^
              " in " ^ random_arguments tys flags budget size next
                (fn (values, final) =>
                  continuation (generated :: values, final)) ^ " end"
            end
        | random_arguments _ _ _ _ _ _ =
            raise Fail "Refute_Extract: random argument shape"

      fun random_constructor (constructor, argument_types) flags =
        random_arguments argument_types flags "budget" "size" "next_state"
          (fn (reversed, final) =>
            let
              val names = reversed
              val values = List.map (fn name =>
                ("#1 " ^ name, "#2 " ^ name)) names
            in
              parens (pair
                (pair (constructor_value constructor values)
                  (constructor_thunk constructor values)) final)
            end)

      fun random_datatype constrs recursive min_size =
        let
          fun weight flags floors =
            if not (List.exists (fn flag => flag) flags) then "1"
            else
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
          val rows = ListPair.zip
            (ListPair.zip (constrs, recursive), min_size)
          val weights = List.map (fn ((_, flags), floors) =>
            weight flags floors) rows
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
          val domain_random = generator_name "rnd_" domain
          val range_random = generator_name "rnd_" range
          val equality = equality_name context domain
          val variable = Term.mk_var
            ("refute_function_argument", domain)
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
          "let\n" ^
          "  val (default_generated, after_default) =\n" ^
          "    " ^ range_random ^ " size state\n" ^
          "  fun draw_points 0 current points = (points, current)\n" ^
          "    | draw_points count current points =\n" ^
          "      let val (point, next) = " ^ domain_random ^
          " size current\n" ^
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
          "            " ^ range_random ^ " size current\n" ^
          "          val graph' = fn x => if " ^ equality ^
          " x point then value else graph x\n" ^
          "      in values rest next graph'\n" ^
          "           ((point_term, value_term) :: updates) end\n" ^
          "  val graph = fn _ => #1 default_generated\n" ^
          "in values points " ^ point_state ^ " graph [] end"
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
        | Refute_Gen.GenDatatype {constrs, recursive, min_size, ...} =>
            random_datatype constrs recursive min_size
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
          ", Int.max (0, size))) (Int.max (0, size)) state\n" ^
          "and " ^ auxiliary ^ " budget size state =\n  " ^ random_body ty
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

      fun random_recovery state fallback =
        parens ("complete := false; if genuine_only then " ^
          parens ("RefuteContinue, " ^ state) ^ " else " ^ fallback)

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
        in
          if is_lazy context then "Susp.force " ^ parens source else source
        end

      fun safe_value expression failure =
        "(case ((SOME (" ^ expression ^ "))\n" ^
        "       handle Match => NONE\n" ^
        "            | Refute_EvalSML.Stuck _ => NONE) of\n" ^
        "   NONE => " ^ failure ^ "\n" ^
        " | SOME refute_value => "

      (* One Split emitter serves both plan compilers; only the recursive
         compile and the match-failure expression differ. *)
      fun split_case recurse failure tm branches environment =
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
                  NONE => failure
                | SOME entry => branch_body entry
              val cons_body = case string_entry "CONS" of
                  NONE => failure
                | SOME (entry as (_, variables, _)) =>
                    (case List.map variable_name variables of
                       [head, tail] =>
                         "let val " ^ head ^
                         " = String.sub (refute_value, 0)\n" ^
                         "    val " ^ tail ^
                         " = String.extract " ^
                         "(refute_value, 1, NONE)\n" ^
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
              "\n | _ => " ^ failure
        in
          safe_value (evaluated_expression tm) failure ^ split_body ^ ")"
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
            List.exists (fn old => Term.aconv old variable) (bound @ seen)
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
                               ("String.sub (" ^ value ^ ", 0)")
                               (thunk ("Refute_EvalSML.char_term " ^
                                 "(String.sub (" ^ value ^ ", 0))")) seen
                           val (tail_pat, tail_guards, tail_bindings,
                                tail_additions, after_tail) =
                             make_pattern tail
                               ("String.extract (" ^ value ^
                                 ", 1, NONE)")
                               (thunk ("Refute_EvalSML.string_term " ^
                                 "(String.extract (" ^ value ^
                                 ", 1, NONE))")) after_head
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
          val checks = guards @ ListPair.mapEq residual (terms, generated)
          val body =
            if null checks then success (additions @ environment)
            else
              safe_value (join " andalso " (map parens checks)) failure ^
              "if refute_value then " ^
              success (additions @ environment) ^ " else " ^ failure ^ ")"
          val body =
            if null bindings then body
            else "let " ^ join "\n    " bindings ^ "\nin " ^ body ^ " end"
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
                ", " ^ genuine_only ^ ")"
              val stuck = recovery "complete" "genuine_only"
                ("refute_hit (" ^ environment_source environment ^
                  ", false)")
            in
              parens ("tests := !tests + 1; " ^
                "if !tests mod 4096 = 0 then " ^
                "Refute_EvalSML.check_deadline () else (); " ^
                safe_value (evaluated_expression tm) stuck ^
                "if refute_value then RefuteContinue else " ^ hit ^ ")")
            end
        | Guard (tm, next) =>
            let
              val (name, flag) = guard_names ()
              val body = compile_exhaustive_plan next environment flag
              val stuck = recovery "complete" "genuine_only"
                (name ^ " false")
            in
              "let fun " ^ name ^ " " ^ flag ^ " = " ^ body ^
              "\nin " ^ safe_value (evaluated_expression tm) stuck ^
              "if refute_value then " ^ name ^ " " ^ genuine_only ^
              " else RefuteContinue) end"
            end
        | SmartGuard {predicate, version, cont} =>
            let
              val (name, flag) = guard_names ()
              val body = compile_exhaustive_plan cont environment flag
              val compiled =
                case compile_smart_guard predicate version environment
                    (name ^ " " ^ genuine_only) "RefuteContinue" of
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
              val alternative = case fallback of
                  NONE => "RefuteContinue"
                | SOME other =>
                    compile_exhaustive_plan other environment "false"
              val stuck = recovery "complete" "genuine_only" alternative
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
                 "!match_failures + 1; RefuteContinue"))
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
                  "RefuteContinue")
              val fuel = Int.max (0, #depth (#qc config))
            in
              parens ("complete := false; " ^ enum_call_name rel mode ^ " " ^
                join " " (map parens generated_inputs) ^
                (if null generated_inputs then "" else " ") ^ callback ^
                " " ^ integer fuel ^ " size complete")
            end

      fun compile_random_plan current environment genuine state =
        case current of
          Prune => parens ("RefuteContinue, " ^ state)
        | Test tm =>
            let
              val hit = "refute_hit (" ^ environment_source environment ^
                ", " ^ genuine ^ ")"
              val stuck = recovery "complete" "genuine_only"
                ("refute_hit (" ^ environment_source environment ^
                  ", false)")
            in
              parens ("tests := !tests + 1; " ^
                "if !tests mod 4096 = 0 then " ^
                "Refute_EvalSML.check_deadline () else (); " ^
                safe_value (evaluated_expression tm) stuck ^
                parens ("if refute_value then RefuteContinue else " ^ hit) ^
                ", " ^ state ^ ")")
            end
        | Guard (tm, next) =>
            let
              val (name, flag) = guard_names ()
              val body = compile_random_plan next environment flag state
              val stuck = random_recovery state (name ^ " false")
            in
              "let fun " ^ name ^ " " ^ flag ^ " = " ^ body ^ "\n" ^
              "in " ^ safe_value (evaluated_expression tm) stuck ^
              "if refute_value then " ^ name ^ " " ^ genuine ^ " else " ^
              parens ("RefuteContinue, " ^ state) ^ ") end"
            end
        | SmartGuard _ =>
            smart_reject "smart Guard reached random compilation"
        | Bind (variable, tm, fallback, next) =>
            let
              val value = variable_name variable
              val term = evaluation_thunk tm environment
              val continued = compile_random_plan next
                ((variable, value, term) :: environment) genuine state
              val alternative = case fallback of
                  NONE => parens ("RefuteContinue, " ^ state)
                | SOME other =>
                    compile_random_plan other environment "false" state
              val failed = random_recovery state alternative
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
                 "!match_failures + 1; " ^
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
                Bool.toString (not (Refute_EvalEnum.has_enum plan)) ^ "\n" ^
              "      val tests = ref 0\n" ^
              "      val match_failures = ref 0\n" ^
              "      val answer = " ^
                compile_exhaustive_plan plan [] "true" ^ "\n" ^
              "      val hit = case answer of RefuteContinue => NONE\n" ^
              "        | RefuteHit found => SOME found\n" ^
              "  in {hit = hit, complete = !complete,\n" ^
              "      table = refute_table_id, state = state, " ^
              "tests = !tests,\n" ^
              "      match_failures = !match_failures}\n" ^
              "  end\n"
          | Random _ =>
              "fun " ^ name ^ " genuine_only size draws state =\n" ^
              "  let val complete = ref true\n" ^
              "      val tests = ref 0\n" ^
              "      val match_failures = ref 0\n" ^
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
              "      tests = !tests, match_failures = !match_failures}\n" ^
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
            "    let val answer = dispatch card genuine_only size draws state\n" ^
            "        val hit = Option.map (fn (environment, genuine) =>\n" ^
            "          (List.map (fn (index, rebuild) =>\n" ^
            "             (index, Refute_EvalSML.wrap_reconstruction\n" ^
            "               refute_table_id rebuild)) environment, genuine))\n" ^
            "          (#hit answer)\n" ^
            "    in {hit = hit, complete = #complete answer,\n" ^
            "        table = refute_table_id, state = #state answer,\n" ^
            "        tests = #tests answer,\n" ^
            "        match_failures = #match_failures answer}\n" ^
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

  fun extract_tests config strategy plans =
    let val {source, entry, ...} =
      extract_tests_with Strict false config strategy plans
    in
      {source = source, entry = entry}
    end

  (* This is the substrate-side test seam, not a narrowing engine.  It lets
     the engine tasks compile a lazy property and supplies a focused unit-test
     entry point while shapes and refinement still live out of tree. *)
  fun extract_lazy_tests config plans =
    let val {source, entry, ...} =
      extract_tests_with Lazy false config Refute_Eval.Narrowing plans
    in
      {source = source, entry = entry}
    end

  (* Compile the first-order bridge between generic narrowing terms and the
     lazy extracted property.  Shapes and search live in Refute_Narrow; only
     these heterogeneously typed conversion functions must be generated. *)
  fun extract_narrowing (config : Refute_Core.config) prefix body =
    let
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
      fun integer value = Int.toString value
      fun term_list values = "[" ^ join ", " values ^ "]"

      val originals = map #2 prefix
      val safe = List.map (fn (index, variable) =>
        Term.mk_var ("refute_bound_" ^ integer index,
          Term.type_of variable)) (Lib.enumerate 0 originals)
      val substitution = ListPair.mapEq (fn (old, fresh) =>
        {redex = old, residue = fresh}) (originals, safe)
      val body = Term.subst substitution body
      val prefix = ListPair.mapEq (fn ((quantifier, _), variable) =>
        (quantifier, variable)) (prefix, safe)

      fun dependencies ty =
        case Refute_Gen.spec_of ty of
            Refute_Gen.GenDatatype {constrs, ...} =>
              List.concat (map #2 constrs)
          | Refute_Gen.GenFun _ =>
              reject ("narrowing cannot generate function type " ^
                type_name ty ^ " before finitization")
          | Refute_Gen.GenCustom _ =>
              reject ("narrowing cannot use a custom generator for " ^
                type_name ty)
          | _ => []
        handle Refute_Gen.NoGenerator (missing, reason) =>
          reject ("no narrowing generator for " ^ type_name missing ^
            " — " ^ reason)

      fun close_types [] seen = rev seen
        | close_types (ty :: rest) seen =
            if List.exists (Util.same_type ty) seen then
              close_types rest seen
            else
              close_types (dependencies ty @ rest) (ty :: seen)
      val types = close_types (map (Term.type_of o #2) prefix) []
      val _ = List.app (fn ty => ignore (ensure_type context ty)) types
      val _ = ignore (ensure_type context Type.bool)

      fun type_index ty = Lib.index (Util.same_type ty) types
      fun conv_name ty = "narrow_conv_" ^ integer (type_index ty)
      fun recon_name ty = "narrow_recon_" ^ integer (type_index ty)
      val witnesses = List.map (fn (index, ty) =>
        Term.mk_var ("refute_narrow_type_" ^ integer index, ty))
        (Lib.enumerate 0 types)
      fun witness_index ty = raw_index (List.nth (witnesses, type_index ty))

      fun lazy body = "Susp.delay (fn () => " ^ body ^ ")"
      fun around_zero index =
        "(if " ^ index ^ " = 0 then 0 else if " ^ index ^
        " mod 2 = 1 then (" ^ index ^ " + 1) div 2 else ~(" ^
        index ^ " div 2))"

      fun primitive_value kind index =
        case kind of
            Refute_Gen.Num => lazy ("IntInf.fromInt " ^ index)
          | Refute_Gen.Int =>
              lazy ("IntInf.fromInt " ^ around_zero index)
          | Refute_Gen.Char => lazy ("Char.chr " ^ index)
          | Refute_Gen.Word _ => lazy ("IntInf.fromInt " ^ index)

      fun primitive_term kind index =
        case kind of
            Refute_Gen.Num =>
              "Refute_EvalSML.num_term (IntInf.fromInt " ^ index ^ ")"
          | Refute_Gen.Int =>
              "Refute_EvalSML.int_term (IntInf.fromInt " ^
              around_zero index ^ ")"
          | Refute_Gen.Char =>
              "Refute_EvalSML.char_term (Char.chr " ^ index ^ ")"
          | Refute_Gen.Word width =>
              "Refute_EvalSML.word_term " ^ integer width ^
              " (IntInf.fromInt " ^ index ^ ")"

      fun constructor_pattern index arguments =
        "(" ^ integer index ^ ", " ^
        term_list (map (fn argument => argument) arguments) ^ ")"

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
                      conv_name arg_ty ^ " depth " ^ argument)
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
          | _ => raise Fail "validated narrowing conversion"

      fun reconstruction_case ty =
        case Refute_Gen.spec_of ty of
            Refute_Gen.GenEnum values =>
              "Refute_EvalSML.raw_term (List.nth (" ^
              term_list (map (integer o raw_index) values) ^
              ", constructor))"
          | Refute_Gen.GenNum kind => primitive_term kind "constructor"
          | Refute_Gen.GenDatatype {constrs, ...} =>
              let
                fun branch (index, (constructor, argument_types)) =
                  let
                    val arguments = List.tabulate (length argument_types,
                      fn number => "argument_" ^ integer number)
                    val rebuilt = ListPair.mapEq (fn (argument, arg_ty) =>
                      recon_name arg_ty ^ " depth " ^ argument)
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
          | _ => raise Fail "validated narrowing reconstruction"

      fun conversion_declaration (index, ty) =
        (if index = 0 then "fun " else "and ") ^ conv_name ty ^
        " depth narrowing_term =\n  case narrowing_term of\n" ^
        "      Refute_Narrow.Narrowing_variable (position, _) =>\n" ^
        "        Refute_EvalSML.lazy_hole position\n" ^
        "    | Refute_Narrow.Narrowing_constructor " ^
        "(constructor, arguments) =>\n        " ^ conversion_case ty

      fun reconstruction_declaration (index, ty) =
        (if index = 0 then "fun " else "and ") ^ recon_name ty ^
        " depth narrowing_term =\n  case narrowing_term of\n" ^
        "      Refute_Narrow.Narrowing_variable _ =>\n" ^
        "        Refute_EvalSML.hole_term " ^ integer (witness_index ty) ^
        "\n    | Refute_Narrow.Narrowing_constructor " ^
        "(constructor, arguments) =>\n        " ^ reconstruction_case ty

      val conversions = join "\n"
        (map conversion_declaration (Lib.enumerate 0 types)) ^ "\n"
      val reconstructions = join "\n"
        (map reconstruction_declaration (Lib.enumerate 0 types)) ^ "\n"

      val body_expression = expression context body
      fun binding (index, ((_, variable), original)) =
        let val ty = Term.type_of variable
        in
          "(" ^ integer (raw_index original) ^ ", fn () => " ^
          recon_name ty ^ " depth (List.nth (arguments, " ^
          integer index ^ ")))"
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
      val bindings = map binding (Lib.enumerate 0 reported_prefix)
      val environment_source = term_list bindings
      val argument_values = map (fn (index, (_, variable)) =>
        conv_name (Term.type_of variable) ^
        " depth (List.nth (arguments, " ^ integer index ^ "))")
        (Lib.enumerate 0 prefix)
      val shapes = map (fn (_, variable) =>
        "Refute_Narrow.shape_of depth (Term.type_of " ^
        "(Refute_EvalSML.raw_term " ^
        integer (witness_index (Term.type_of variable)) ^ "))") prefix
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
        "  end\n"

      val engine =
        if has_existential then
          "val initial = Refute_Narrow.tree_of " ^ tree_prefix ^ "\n" ^
          "val result = Refute_Narrow.refute_pnf genuine_only depth\n" ^
          "  (narrow_evaluate depth) initial\n" ^
          "val (hit, tests) =\n" ^
          "  case result of\n" ^
          "      Refute_Narrow.PnfCounterexample\n" ^
          "        {genuine, example, tests, ...} =>\n" ^
          "        let val arguments = Refute_Narrow.leading_universals " ^
          integer leading_count ^ " example\n" ^
          "        in (make_hit depth arguments genuine, tests) end\n" ^
          "    | Refute_Narrow.PnfExhausted {tests, ...} => (NONE, tests)\n"
        else
          "val result = Refute_Narrow.refute_plain_avoiding genuine_only\n" ^
          "  {arguments = " ^ initial_arguments ^ ",\n" ^
          "   evaluate = narrow_evaluate depth,\n" ^
          "   accept = accept_hit depth genuine_only}\n" ^
          "val (hit, tests) =\n" ^
          "  case result of\n" ^
          "      Refute_Narrow.PlainCounterexample\n" ^
          "        {genuine, arguments, tests} =>\n" ^
          "        (make_hit depth arguments genuine, tests)\n" ^
          "    | Refute_Narrow.PlainExhausted {tests} => (NONE, tests)\n"

      val table_id = Refute_EvalSML.register_term_tables
        (rev (!(#list constructor_terms))) (rev (!(#list raw_terms)))
      fun finish () =
        let
          val _ = drain_definitions context
          val runtime =
            "val refute_table_id = " ^ integer table_id ^ "\n" ^
            "fun candidate depth arguments genuine =\n" ^
            "  (" ^ environment_source ^ ", genuine)\n" ^
            "fun accept_hit depth genuine_only arguments genuine =\n" ^
            "  (not genuine_only orelse Refute_Narrow.all_ground arguments)\n" ^
            "  andalso not ((!Refute_EvalSML.ignored_filter)\n" ^
            "    (candidate depth arguments genuine))\n" ^
            "fun make_hit depth arguments genuine =\n" ^
            "  let val found = candidate depth arguments genuine\n" ^
            "  in if (!Refute_EvalSML.ignored_filter) found then NONE\n" ^
            "     else SOME found\n  end\n" ^
            "fun dispatch card genuine_only depth draws state =\n" ^
            "  if card <> 1 then raise Subscript else\n" ^
            "  let\n    " ^ engine ^
            "  in {hit = hit, complete = false, table = refute_table_id,\n" ^
            "      state = state, tests = tests, match_failures = 0}\n" ^
            "  end\n" ^
            "fun protected_dispatch card genuine_only depth draws state =\n" ^
            "  Refute_EvalSML.with_term_tables refute_table_id (fn () =>\n" ^
            "    let val answer = dispatch card genuine_only depth draws state\n" ^
            "        val hit = Option.map (fn (environment, genuine) =>\n" ^
            "          (List.map (fn (index, rebuild) =>\n" ^
            "             (index, Refute_EvalSML.wrap_reconstruction\n" ^
            "               refute_table_id rebuild)) environment, genuine))\n" ^
            "          (#hit answer)\n" ^
            "    in {hit = hit, complete = #complete answer,\n" ^
            "        table = refute_table_id, state = #state answer,\n" ^
            "        tests = #tests answer,\n" ^
            "        match_failures = #match_failures answer}\n" ^
            "    end)\n" ^
            "fun install () = Refute_EvalSML.installed_dispatch :=\n" ^
            "  SOME protected_dispatch\n"
          val source = source_prefix context ^
            definition_declarations context ^ "\n" ^ conversions ^
            reconstructions ^ evaluate ^ runtime
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

  fun safe_exception_text error =
    ((case General.exnMessage error of
          "" => "unknown extraction exception"
        | text => text)
     handle Interrupt => raise Interrupt
          | _ => "unknown extraction exception")

  (* This is the same extraction and scope validator used by native compile,
     run in strict gate mode over the complete plan set.  Evaluation terms are
     not executable plan nodes, so validate them separately without granting
     the smart-Guard relation exception.  Each extraction returns its exact
     table ID: concurrent preflights and compiles therefore clean only their
     own registrations, without nesting the non-recursive compile mutex.

     The registration callback is a private test seam.  The production entry
     point supplies an inert callback, so it cannot change normal behavior. *)
  fun native_preflight_with registration_callback config strategy plans
      evals =
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

      fun report (result, cleanup_result) =
        case (result, cleanup_result) of
            (Exn.Exn Interrupt, _) => raise Interrupt
          | (_, Exn.Exn Interrupt) => raise Interrupt
          | (Exn.Res _, Exn.Res _) => []
          | (Exn.Exn (NotExtractable reasons), Exn.Res _) => reasons
          | (Exn.Exn error, Exn.Res _) =>
              ["native preflight: " ^ safe_exception_text error]
          | (Exn.Res _, Exn.Exn error) =>
              ["native preflight cleanup: " ^ safe_exception_text error]
          | (Exn.Exn (NotExtractable reasons), Exn.Exn error) =>
              reasons @
              ["native preflight cleanup: " ^ safe_exception_text error]
          | (Exn.Exn error, Exn.Exn cleanup_error) =>
              ["native preflight: " ^ safe_exception_text error,
               "native preflight cleanup: " ^
                 safe_exception_text cleanup_error]
    in
      case Exn.capture (fn () =>
          extract_tests_with Strict true config strategy plans) () of
          Exn.Exn Interrupt => raise Interrupt
        | Exn.Exn (NotExtractable reasons) => reasons
        | Exn.Exn error =>
            ["native preflight: " ^ safe_exception_text error]
        | Exn.Res {table, ...} =>
            let
              val result = Exn.capture (fn () =>
                (registration_callback table;
                 List.app validate_eval evals)) ()
              val cleanup_result = Exn.capture
                Refute_EvalSML.unregister_term_tables table
            in
              report (result, cleanup_result)
            end
    end

  fun native_preflight config strategy plans evals =
    native_preflight_with (fn _ => ()) config strategy plans evals

  fun install_extractor () = Refute_EvalSML.extract_tests_hook :=
    (fn extraction_mode => fn config => fn strategy => fn problem =>
      let
        val mode = case extraction_mode of
            Refute_EvalSML.StrictExtraction => Strict
          | Refute_EvalSML.LazyExtraction => Lazy
        val extracted = case problem of
            Refute_Eval.Plans plans =>
              extract_tests_with mode false config strategy plans
          | Refute_Eval.Pnf {prefix, body} =>
              if strategy = Refute_Eval.Narrowing andalso mode = Lazy then
                extract_narrowing config prefix body
              else
                raise NotExtractable
                  ["narrowing requires the native lazy substrate"]
      in
        Refute_EvalSML.Extracted extracted
      end
      handle NotExtractable reasons =>
               Refute_EvalSML.ExtractionFailed reasons
           | Interrupt => raise Interrupt)

  val _ = install_extractor ()
end
