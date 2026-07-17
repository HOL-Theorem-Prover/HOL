structure Refute_Extract = struct
  type term = Term.term
  type hol_type = Type.hol_type

  exception NotExtractable of string list

  type extraction =
    { source : string,
      entry : string }

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

  fun same_type left right = Type.compare (left, right) = EQUAL
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
    { datatypes : datatype_desc list ref,
      types : (hol_type * ml_ty * string) list ref,
      definitions : (term * string * Thm.thm) list ref,
      definition_groups : term list list ref,
      definition_clauses : (term * string) list ref,
      pending : term list ref,
      compset_items :
        ((string * string) * computeLib.transform list) list option ref,
      next_type : int ref,
      next_const : int ref }

  fun new_context () : context =
    { datatypes = ref [],
      types = ref [],
      definitions = ref [],
      definition_groups = ref [],
      definition_clauses = ref [],
      pending = ref [],
      compset_items = ref NONE,
      next_type = ref 0,
      next_const = ref 0 }

  fun lookup_type ({types, ...} : context) ty =
    case List.find (fn (other, _, _) => same_type other ty) (!types) of
      SOME (_, mlty, equality) => SOME (mlty, equality)
    | NONE => NONE

  fun lookup_datatype ({datatypes, ...} : context) ty =
    List.find (fn info => same_type (#hol_ty info) ty) (!datatypes)

  fun fresh_type ({next_type, ...} : context) =
    let val number = !next_type
        val _ = next_type := number + 1
    in "refute_ty_" ^ Int.toString number end

  fun fresh_const ({next_const, ...} : context) base =
    let val number = !next_const
        val _ = next_const := number + 1
    in lower_name base ^ "_" ^ Int.toString number end

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

  fun is_char_list ty = same_type ty stringSyntax.string_ty

  fun classify_primitive context ty =
    if Type.is_vartype ty then
      SOME (MLVar (clean_name (Type.dest_vartype ty)))
    else if same_type ty Type.bool then SOME MLBool
    else if same_type ty numSyntax.num then SOME MLIntInf
    else if same_type ty intSyntax.int_ty then SOME MLIntInf
    else if same_type ty stringSyntax.char_ty then SOME MLChar
    else if is_char_list ty then SOME MLString
    else if same_type ty oneSyntax.one_ty then SOME MLUnit
    else if wordsSyntax.is_word_type ty then SOME (MLWord (word_width ty))
    else
      case Lib.total Type.dom_rng ty of
        SOME (domain, range) =>
          SOME (MLArrow (ensure_type context domain,
                         ensure_type context range))
      | NONE =>
          (case Lib.total pairSyntax.dest_prod ty of
             SOME (left, right) =>
               SOME (MLTuple
                 [ensure_type context left, ensure_type context right])
           | NONE =>
               (case Lib.total listSyntax.dest_list_type ty of
                  SOME element => SOME (MLList (ensure_type context element))
                | NONE =>
                    (case Lib.total optionSyntax.dest_option ty of
                       SOME element =>
                         SOME (MLOption (ensure_type context element))
                     | NONE => NONE)))

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
                val mlty = MLDatatype ml_name
                val _ = #types context :=
                  (ty, mlty, equality) :: !(#types context)
                fun constructor_info constructor =
                  let
                    val (arguments, result) =
                      boolSyntax.strip_fun (Term.type_of constructor)
                    val _ =
                      if same_type result ty then ()
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

  fun equality_name context ty =
    (ignore (ensure_type context ty);
     case lookup_type context ty of
       SOME (_, name) => name
     | NONE => raise Fail "Refute_Extract: missing equality name")

  fun datatype_dependencies context ({hol_ty, constructors, ...} :
      datatype_desc) =
    let
      fun collect ty =
        case lookup_datatype context ty of
          SOME info =>
            if same_type hol_ty (#hol_ty info) then [] else [#hol_ty info]
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
        if List.exists (same_type ty) seen then false
        else if same_type ty target then true
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
        List.exists (fn info => same_type (#hol_ty info) ty) group
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
      fun constructor_values (_, arguments, name) =
        let
          fun build [] variables =
                let val value = case variables of
                      [] => name
                    | [variable] => name ^ " " ^ variable
                    | _ => name ^ " (" ^ join ", " variables ^ ")"
                in "[" ^ value ^ "]" end
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
    in
      if same_type ty Type.bool then "[false, true]"
      else if same_type ty oneSyntax.one_ty then "[()]"
      else if same_type ty stringSyntax.char_ty then
        "List.tabulate (256, Char.chr)"
      else if wordsSyntax.is_word_type ty andalso word_width ty <= 8 then
        let val count = IntInf.toInt (IntInf.pow (2, word_width ty))
        in
          "List.tabulate (" ^ Int.toString count ^
          ", fn n => IntInf.fromInt n)"
        end
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
             | NONE =>
                 case lookup_datatype context ty of
                   SOME {constructors, ...} =>
                     (case Refute_Gen.cardinality ty of
                        NONE => nonenumerable ()
                      | SOME _ =>
                          "List.concat [" ^ join ", "
                            (List.map constructor_values constructors) ^ "]")
                 | NONE => nonenumerable ())
    end

  fun equality_body context ty left right =
    let val mlty = ensure_type context ty
    in
      case mlty of
        MLBool =>
          parens ("(" ^ left ^ " andalso " ^ right ^ ") orelse " ^
                  "(not " ^ left ^ " andalso not " ^ right ^ ")")
      | MLIntInf =>
          "IntInf.compare (" ^ left ^ ", " ^ right ^ ") = EQUAL"
      | MLChar => "Char.compare (" ^ left ^ ", " ^ right ^ ") = EQUAL"
      | MLString =>
          "String.compare (" ^ left ^ ", " ^ right ^ ") = EQUAL"
      | MLUnit => "true"
      | MLWord _ =>
          "IntInf.compare (" ^ left ^ ", " ^ right ^ ") = EQUAL"
      | MLTuple [left_ty, right_ty] =>
          let
            val (hol_left, hol_right) = pairSyntax.dest_prod ty
            val eq_left = equality_name context hol_left
            val eq_right = equality_name context hol_right
          in
            "(case (" ^ left ^ ", " ^ right ^ ") of " ^
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
            "in loop " ^ left ^ " " ^ right ^ " end"
          end
      | MLOption _ =>
          let
            val element = optionSyntax.dest_option ty
            val eq_element = equality_name context element
          in
            "(case (" ^ left ^ ", " ^ right ^ ") of " ^
            "(NONE, NONE) => true | (SOME a, SOME b) => " ^
            eq_element ^ " a b | _ => false)"
          end
      | MLArrow (domain, _) =>
          let
            val (domain_ty, range_ty) = Type.dom_rng ty
            val eq_range = equality_name context range_ty
          in
            "List.all (fn z => " ^ eq_range ^ " (" ^ left ^ " z) (" ^
            right ^ " z)) " ^ parens (enum_expression context domain_ty)
          end
      | MLDatatype _ => datatype_equality context ty left right
      | MLVar _ =>
          reject ("cannot generate structural equality for type variable " ^
                  type_name ty)
      | MLTuple _ => raise Fail "Refute_Extract: malformed tuple type"
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
    in
      "(case (" ^ left ^ ", " ^ right ^ ") of " ^
      join " | " (List.map clause (#constructors info)) ^
      " | _ => false)"
    end

  fun equality_declarations context =
    let
      val types = rev (!(#types context))
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
      fun build_custom name = with_arity arguments arity (custom name)
    in
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
          constructor_expression context head (List.map (pattern context)
            arguments)
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

  fun primitive context head argument_terms arguments =
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

  fun expression context term =
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

  fun definition_clause context (constant, name, theorem) =
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
    String.concat (List.map (datatype_declaration context)
      (datatype_groups context)) ^ "\n" ^
    equality_declarations context ^ "\n"

  fun compile_types types =
    let
      val context = new_context ()
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

  fun compile_type ty = compile_types [ty]

  fun extract_term term =
    let
      val context = new_context ()
      val _ = ignore (ensure_type context (Term.type_of term))
      val entry_expression = expression context term
      val _ = drain_definitions context
      val source = source_prefix context ^
        definition_declarations context ^ "\nfun entry () = " ^
        entry_expression ^ "\n"
    in
      {source = source, entry = "entry ()"}
    end

  fun extract_tests (_ : Refute_Core.config) strategy plans : extraction =
    let
      open Refute_Eval

      val context = new_context ()
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
        | Prune => Prune

      val plans = List.map (fn plan => rename_plan plan []) plans

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
        List.exists (fn (other, _) => same_type other ty)
          (!(Refute_Gen.abstract_specs))

      val validated = ref ([] : hol_type list)

      fun validate_type root ty =
        if List.exists (same_type ty) (!validated) then ()
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
                 | Exhaustive => ())
            | _ => ()
          end
          handle Refute_Gen.NoGenerator (missing, why) =>
            reject ("no generator for " ^ type_name missing ^ " — " ^ why)

      val root_types = Lib.mk_set (List.concat (List.map plan_gen_types plans))
      val _ = List.app (fn ty => validate_type ty ty) root_types

      fun dependencies ty =
        case Refute_Gen.spec_of ty of
          Refute_Gen.GenDatatype {constrs, ...} =>
            List.concat (List.map #2 constrs)
        | Refute_Gen.GenFun (domain, range) => [domain, range]
        | _ => []

      fun close_types [] seen = rev seen
        | close_types (ty :: rest) seen =
            if List.exists (same_type ty) seen then close_types rest seen
            else close_types (dependencies ty @ rest) (ty :: seen)

      val generator_types = close_types root_types []
      val _ = List.app (fn ty => ignore (ensure_type context ty))
        generator_types

      fun generator_name prefix ty =
        let
          val index = Lib.index (same_type ty) generator_types
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
          safe_value (expression context tm) failure ^ split_body ^ ")"
        end

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
                safe_value (expression context tm) stuck ^
                "if refute_value then RefuteContinue else " ^ hit ^ ")")
            end
        | Guard (tm, next) =>
            let
              val (name, flag) = guard_names ()
              val body = compile_exhaustive_plan next environment flag
              val stuck = recovery "complete" "genuine_only"
                (name ^ " false")
            in
              "let fun " ^ name ^ " " ^ flag ^ " = " ^ body ^ "\n" ^
              "in " ^ safe_value (expression context tm) stuck ^
              "if refute_value then " ^ name ^ " " ^ genuine_only ^
              " else RefuteContinue) end"
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
              safe_value (expression context tm) stuck ^
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
                safe_value (expression context tm) stuck ^
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
              "in " ^ safe_value (expression context tm) stuck ^
              "if refute_value then " ^ name ^ " " ^ genuine ^ " else " ^
              parens ("RefuteContinue, " ^ state) ^ ") end"
            end
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
              safe_value (expression context tm) failed ^
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

      fun card_declaration (index, plan) =
        let
          val number = index + 1
          val name = "card_" ^ integer number
        in
          case strategy of
            Exhaustive =>
              "fun " ^ name ^ " genuine_only size draws state =\n" ^
              "  let val complete = ref true\n" ^
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
            | Prune => ()
        in payload plan end) plans
      val cards = String.concat
        (List.map card_declaration (Lib.enumerate 0 plans))
      val table_id = Refute_EvalSML.register_term_tables
        (rev (!(#list constructor_terms))) (rev (!(#list raw_terms)))
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
        definition_declarations context ^ "\n" ^ generator_runtime ^ "\n" ^
        exhaustive_generators ^ random_generators ^ table_declaration ^
        cards ^ dispatch
    in
      {source = source, entry = "install ()"}
    end

  fun install_extractor () = Refute_EvalSML.extract_tests_hook :=
    (fn config => fn strategy => fn plans =>
      let
        val table = !Refute_EvalSML.table_serial
        fun cleanup () =
          if !Refute_EvalSML.table_serial = table then ()
          else Refute_EvalSML.unregister_term_tables table
      in
        let val {source, entry} = extract_tests config strategy plans
        in
          Refute_EvalSML.Extracted
            {source = source, entry = entry, table = table}
        end
        handle NotExtractable reasons =>
                 (cleanup ();
                  Refute_EvalSML.ExtractionFailed reasons)
             | Interrupt => (cleanup (); raise Interrupt)
             | error => (cleanup (); raise error)
      end)

  val _ = install_extractor ()
end
