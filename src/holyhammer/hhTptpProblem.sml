structure hhTptpProblem :> hhTptpProblem =
struct

  datatype tptp_type =
      TyCon of string * tptp_type list
    | TyVar of string
    | TyFun of tptp_type * tptp_type
    | TyPi of string list * tptp_type

  datatype tptp_term =
      Tm of (string * tptp_type list) * tptp_term list
    | TmAbs of (string * tptp_type) * tptp_term

  datatype conn = Not | And | Or | Implies | Iff | Equal

  datatype tptp_formula =
      Quant of bool * (string * tptp_type option) list * tptp_formula
    | TyQuant of bool * string list * tptp_formula
    | Conn of conn * tptp_formula list
    | Atom of tptp_term

  type syntax = {with_ite : bool, with_let : bool}
  datatype fool = NoFool | Fool of syntax
  datatype format =
      FOF
    | TFF of {poly : bool, fool : fool}
    | THF of {poly : bool, syntax : syntax, choice : bool}
  datatype role = Axiom | Hypothesis | Definition | Conjecture
  datatype line =
      TypeDecl of string * string * int
    | SymDecl of string * string * tptp_type
    | FormLine of string * role * tptp_formula
  type problem = (string * line list) list

  fun fail message = raise Fail ("hhTptpProblem: " ^ message)

  val join = String.concatWith

  fun is_higher FOF = false
    | is_higher (TFF _) = false
    | is_higher (THF _) = true

  fun is_typed FOF = false
    | is_typed _ = true

  fun is_poly FOF = false
    | is_poly (TFF {poly, ...}) = poly
    | is_poly (THF {poly, ...}) = poly

  fun syntax_of FOF = {with_ite = false, with_let = false}
    | syntax_of (TFF {fool = NoFool, ...}) =
        {with_ite = false, with_let = false}
    | syntax_of (TFF {fool = Fool syntax, ...}) = syntax
    | syntax_of (THF {syntax, ...}) = syntax

  fun format_name FOF = "fof"
    | format_name (TFF _) = "tff"
    | format_name (THF _) = "thf"

  fun role_name Axiom = "axiom"
    | role_name Hypothesis = "hypothesis"
    | role_name Definition = "definition"
    | role_name Conjecture = "conjecture"

  fun is_sort (TyCon _) = true
    | is_sort (TyVar _) = true
    | is_sort _ = false

  fun uncurry (TyPi (vars, ty)) = TyPi (vars, uncurry ty)
    | uncurry (ty as TyFun (left, right)) =
        if not (is_sort left) then ty
        else
          (case uncurry right of
             TyFun (TyCon ("*", args), result) =>
               TyFun (TyCon ("*", left :: args), result)
           | TyFun (right', result) =>
               if is_sort right' then
                 TyFun (TyCon ("*", [left, right']), result)
               else ty
           | _ => ty)
    | uncurry ty = ty

  fun string_of_type format ty =
    let
      fun str rhs (TyCon (name, [])) = name
        | str _ (TyVar name) = name
        | str _ (TyCon ("*", tys)) =
            "(" ^ join " * " (map (str false) tys) ^ ")"
        | str _ (TyCon (name, tys)) =
            if is_higher format then
              "(" ^ join " @ " (name :: map (str false) tys) ^ ")"
            else name ^ "(" ^ join "," (map (str false) tys) ^ ")"
        | str rhs (TyFun (left, right)) =
            let val text = str false left ^ " > " ^ str true right in
              if rhs then text else "(" ^ text ^ ")"
            end
        | str _ (TyPi (vars, body)) =
            "!>[" ^ join ", " (map (fn name => name ^ " : $tType") vars) ^
            "]: " ^ str false body
    in
      str true (if is_higher format then ty else uncurry ty)
    end

  fun string_of_bound_var format (name, NONE) =
        if is_typed format then name ^ " : $i" else name
    | string_of_bound_var format (name, SOME ty) =
        if is_typed format then name ^ " : " ^ string_of_type format ty
        else name

  fun check_special format name =
    let val {with_ite, with_let} = syntax_of format in
      if name = "$ite" andalso not with_ite then
        fail "$ite is not enabled for this format"
      else if name = "$let" andalso not with_let then
        fail "$let is not enabled for this format"
      else if name = "@+" orelse name = "@@+" then
        fail "choice is not supported"
      else ()
    end

  fun string_of_application format head args =
    if null args then head
    else if is_higher format then
      "(" ^ join " @ " (head :: args) ^ ")"
    else
      head ^ "(" ^ join "," args ^ ")"

  fun string_of_term format (Tm ((name, tys), terms)) =
        let
          val _ = check_special format name
        in
          if name = "$ite" then
            (case terms of
               [cond, then_tm, else_tm] =>
                 "$ite(" ^ string_of_term format cond ^ "," ^
                 string_of_term format then_tm ^ "," ^
                 string_of_term format else_tm ^ ")"
             | _ => fail "$ite needs exactly three term arguments")
          else if name = "$let" then
            (case terms of
               [value, TmAbs ((var, ty), body)] =>
                 "$let(" ^ var ^ " : " ^ string_of_type format ty ^ ", " ^
                 var ^ " := " ^ string_of_term format value ^ ", " ^
                 string_of_term format body ^ ")"
             | _ => fail "$let needs a value and a lambda abstraction")
          else
            let
              val types = map (string_of_type format) tys
              val types' =
                if is_higher format then
                  map (fn ty => "(" ^ ty ^ ")") types
                else types
              val args = types' @ map (string_of_term format) terms
            in
              string_of_application format name args
            end
        end
    | string_of_term (format as THF _) (TmAbs ((name, ty), body)) =
        "(^[" ^ name ^ " : " ^ string_of_type format ty ^ "]: " ^
        string_of_term format body ^ ")"
    | string_of_term _ (TmAbs _) =
        fail "lambda abstraction in a first-order format"

  fun conn_name Not = "~"
    | conn_name And = "&"
    | conn_name Or = "|"
    | conn_name Implies = "=>"
    | conn_name Iff = "<=>"
    | conn_name Equal = "="

  fun string_of_formula format (Quant (all, vars, body)) =
        "(" ^ (if all then "!" else "?") ^ "[" ^
        join ", " (map (string_of_bound_var format) vars) ^ "]: " ^
        string_of_formula format body ^ ")"
    | string_of_formula format (TyQuant (all, vars, body)) =
        if is_poly format then
          "(" ^ (if all then "!>" else "?>") ^ "[" ^
          join ", " (map (fn name => name ^ " : $tType") vars) ^ "]: " ^
          string_of_formula format body ^ ")"
        else fail "type quantifier in a monomorphic format"
    | string_of_formula format
        (Conn (Not, [Conn (Equal, [Atom left, Atom right])])) =
        "(" ^ string_of_term format left ^ " != " ^
        string_of_term format right ^ ")"
    | string_of_formula format (Conn (Not, [body])) =
        "(~ " ^ string_of_formula format body ^ ")"
    | string_of_formula format (Conn (Equal, [Atom left, Atom right])) =
        "(" ^ string_of_term format left ^ " = " ^
        string_of_term format right ^ ")"
    | string_of_formula format (Conn (conn, bodies)) =
        if null bodies then fail "connective has no operands"
        else if conn = Not orelse conn = Equal then
          fail "connective has the wrong number of operands"
        else "(" ^ join (" " ^ conn_name conn ^ " ")
          (map (string_of_formula format) bodies) ^ ")"
    | string_of_formula format (Atom term) = string_of_term format term

  fun nary_type 0 = TyCon ("$tType", [])
    | nary_type n = TyFun (TyCon ("$tType", []), nary_type (n - 1))

  fun string_of_line format (TypeDecl (ident, tyop, arity)) =
        if is_typed format then
          format_name format ^ "(" ^ ident ^ ", type,\n    " ^ tyop ^ " : " ^
          string_of_type format (nary_type arity) ^ ").\n"
        else fail "type declaration in FOF"
    | string_of_line format (SymDecl (ident, symbol, ty)) =
        if is_typed format then
          format_name format ^ "(" ^ ident ^ ", type,\n    " ^ symbol ^ " : " ^
          string_of_type format ty ^ ").\n"
        else fail "symbol declaration in FOF"
    | string_of_line format (FormLine (ident, role, formula)) =
        format_name format ^ "(" ^ ident ^ ", " ^ role_name role ^ ",\n    (" ^
        string_of_formula format formula ^ ")).\n"

  fun string_of_section format (heading, lines) =
    "% " ^ heading ^ " (" ^ Int.toString (length lines) ^ ")\n" ^
    String.concat (map (string_of_line format) lines)

  fun string_of_problem format header sections =
    "% " ^ header ^ "\n" ^
    String.concat (map (string_of_section format) sections)

  fun fact_name 1 fact = "thm." ^ fact
    | fact_name copy fact = "thm" ^ Int.toString copy ^ "." ^ fact

  fun fact_of_name name =
    if String.isPrefix "thm" name then
      let
        val start = String.size "thm"
        fun digits index =
          if index < String.size name andalso
             Char.isDigit (String.sub (name, index)) then digits (index + 1)
          else index
        val stop = digits start
      in
        if stop < String.size name andalso String.sub (name, stop) = #"."
        then SOME (String.extract (name, stop + 1, NONE))
        else NONE
      end
    else NONE

end
