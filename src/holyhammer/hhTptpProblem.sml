(* ========================================================================= *)
(* FILE          : hhTptpProblem.sml                                         *)
(* DESCRIPTION   : TPTP problem syntax and printer                           *)
(* PORTED FROM   : Isabelle's atp_problem.ML (Jia Meng, Jasmin Blanchette,   *)
(*                 Martin Desharnais): the TPTP syntax tree, simplified, and *)
(*                 the printed syntax.  The printer is new.                  *)
(* ========================================================================= *)

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

  (* Printers build the text as reversed fragment lists: each takes the
     fragments emitted so far and returns them extended, in one left to
     right traversal; string_of_problem concatenates once. *)

  fun join_into sep emit acc [] = acc
    | join_into sep emit acc (x :: xs) =
        let
          fun loop acc [] = acc
            | loop acc (x :: xs) = loop (emit (sep :: acc) x) xs
        in
          loop (emit acc x) xs
        end

  fun type_into format acc ty =
    let
      fun str rhs acc (TyCon (name, [])) = name :: acc
        | str _ acc (TyVar name) = name :: acc
        | str _ acc (TyCon ("*", tys)) =
            ")" :: join_into " * " (str false) ("(" :: acc) tys
        | str _ acc (TyCon (name, tys)) =
            if is_higher format then
              ")" ::
              List.foldl (fn (ty, acc) => str false (" @ " :: acc) ty)
                (name :: "(" :: acc) tys
            else
              ")" :: join_into "," (str false) ("(" :: name :: acc) tys
        | str rhs acc (TyFun (left, right)) =
            let
              val acc = if rhs then acc else "(" :: acc
              val acc = str true (" > " :: str false acc left) right
            in
              if rhs then acc else ")" :: acc
            end
        | str _ acc (TyPi (vars, body)) =
            str false
              ("]: " ::
               join_into ", " (fn acc => fn name => " : $tType" :: name :: acc)
                 ("!>[" :: acc) vars)
              body
    in
      str true acc (if is_higher format then ty else uncurry ty)
    end

  fun bound_var_into format acc (name, NONE) =
        if is_typed format then " : $i" :: name :: acc else name :: acc
    | bound_var_into format acc (name, SOME ty) =
        if is_typed format then type_into format (" : " :: name :: acc) ty
        else name :: acc

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

  fun term_into format acc (Tm ((name, tys), terms)) =
        let
          val _ = check_special format name
        in
          if name = "$ite" then
            (case terms of
               [cond, then_tm, else_tm] =>
                 let
                   val acc = term_into format ("$ite(" :: acc) cond
                   val acc = term_into format ("," :: acc) then_tm
                 in
                   ")" :: term_into format ("," :: acc) else_tm
                 end
             | _ => fail "$ite needs exactly three term arguments")
          else if name = "$let" then
            (case terms of
               [value, TmAbs ((var, ty), body)] =>
                 let
                   val acc = type_into format
                     (" : " :: var :: "$let(" :: acc) ty
                   val acc = term_into format
                     (" := " :: var :: ", " :: acc) value
                 in
                   ")" :: term_into format (", " :: acc) body
                 end
             | _ => fail "$let needs a value and a lambda abstraction")
          else if null tys andalso null terms then name :: acc
          else
            let
              val higher = is_higher format
              val sep = if higher then " @ " else ","
              fun separate first acc =
                if first andalso not higher then acc else sep :: acc
              fun ty_into acc ty =
                if higher then ")" :: type_into format ("(" :: acc) ty
                else type_into format acc ty
              fun tys_into first acc [] = (first, acc)
                | tys_into first acc (ty :: rest) =
                    tys_into false (ty_into (separate first acc) ty) rest
              fun tms_into first acc [] = acc
                | tms_into first acc (tm :: rest) =
                    tms_into false (term_into format (separate first acc) tm)
                      rest
              val (first, acc) =
                tys_into true
                  (if higher then name :: "(" :: acc
                   else "(" :: name :: acc) tys
            in
              ")" :: tms_into first acc terms
            end
        end
    | term_into (format as THF _) acc (TmAbs ((name, ty), body)) =
        ")" :: term_into format
          (": " :: "]" :: type_into format (" : " :: name :: "(^[" :: acc) ty)
          body
    | term_into _ _ (TmAbs _) =
        fail "lambda abstraction in a first-order format"

  fun conn_name Not = "~"
    | conn_name And = "&"
    | conn_name Or = "|"
    | conn_name Implies = "=>"
    | conn_name Iff = "<=>"
    | conn_name Equal = "="

  fun formula_into format acc (Quant (all, vars, body)) =
        ")" :: formula_into format
          ("]: " ::
           join_into ", " (bound_var_into format)
             ((if all then "![" else "?[") :: "(" :: acc) vars)
          body
    (* A TFF formula binds its type variables with the ordinary
       quantifiers; !> and ?> are for THF formulas and for symbol types. *)
    | formula_into format acc (TyQuant (all, vars, body)) =
        if is_poly format then
          ")" :: formula_into format
            ("]: " ::
             join_into ", " (fn acc => fn name => " : $tType" :: name :: acc)
               ((case (is_higher format, all) of
                     (true, true) => "!>["
                   | (true, false) => "?>["
                   | (false, true) => "!["
                   | (false, false) => "?[") :: "(" :: acc) vars)
            body
        else fail "type quantifier in a monomorphic format"
    | formula_into format acc
        (Conn (Not, [Conn (Equal, [Atom left, Atom right])])) =
        ")" :: term_into format
          (" != " :: term_into format ("(" :: acc) left) right
    | formula_into format acc (Conn (Not, [body])) =
        ")" :: formula_into format ("(~ " :: acc) body
    | formula_into format acc (Conn (Equal, [Atom left, Atom right])) =
        ")" :: term_into format
          (" = " :: term_into format ("(" :: acc) left) right
    | formula_into format acc (Conn (conn, bodies)) =
        if null bodies then fail "connective has no operands"
        else if conn = Not orelse conn = Equal then
          fail "connective has the wrong number of operands"
        else
          ")" :: join_into (" " ^ conn_name conn ^ " ") (formula_into format)
            ("(" :: acc) bodies
    | formula_into format acc (Atom term) = term_into format acc term

  fun nary_type 0 = TyCon ("$tType", [])
    | nary_type n = TyFun (TyCon ("$tType", []), nary_type (n - 1))

  fun line_into format acc (TypeDecl (ident, tyop, arity)) =
        if is_typed format then
          ").\n" :: type_into format
            (" : " :: tyop :: ", type,\n    " :: ident :: "(" ::
             format_name format :: acc)
            (nary_type arity)
        else fail "type declaration in FOF"
    | line_into format acc (SymDecl (ident, symbol, ty)) =
        if is_typed format then
          ").\n" :: type_into format
            (" : " :: symbol :: ", type,\n    " :: ident :: "(" ::
             format_name format :: acc)
            ty
        else fail "symbol declaration in FOF"
    | line_into format acc (FormLine (ident, role, formula)) =
        ")).\n" :: formula_into format
          (",\n    (" :: role_name role :: ", " :: ident :: "(" ::
           format_name format :: acc)
          formula

  fun section_into format acc (heading, lines) =
    List.foldl (fn (line, acc) => line_into format acc line)
      (")\n" :: Int.toString (length lines) :: " (" :: heading :: "% " :: acc)
      lines

  fun string_of_fragments acc = String.concat (rev acc)

  fun string_of_problem format header sections =
    string_of_fragments
      (List.foldl (fn (section, acc) => section_into format acc section)
         ["\n", header, "% "] sections)

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
