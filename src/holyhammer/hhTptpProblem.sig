signature hhTptpProblem =
sig

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

  val syntax_of : format -> syntax
  val format_name : format -> string
  val string_of_problem : format -> string -> problem -> string

  (* Unescaped TPTP names of premise copies: copy 1 of a fact is
     thm.<fact>, copy n > 1 (a monomorphic instance) is thm<n>.<fact>.
     fact_of_name inverts fact_name and is NONE for other names. *)
  val fact_name : int -> string -> string
  val fact_of_name : string -> string option

end
