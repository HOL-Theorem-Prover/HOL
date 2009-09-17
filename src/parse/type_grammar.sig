signature type_grammar =
sig

(* HOL-Omega concrete syntax (suggestive; without infixes, arrays, etc.:

Type is the root nonterminal.

Type   ::= TApp | Type TApp
TApp   ::= Leaf | Tuple TApp
Leaf   ::= string | '(' Type ')'
Tuple ::= '(' Type ',' TupR ')'
TupR  ::= Type | Type ',' TupR

Could be
TApp   ::= Leaf | Tuple Leaf

*)

  datatype grammar_rule
    = CONSTANT of string list
    | BINDER of string list list
    | APPLICATION
    | CAST
    | ARRAY_SFX
    | INFIX of {opname : string, parse_string : string} list *
                HOLgrammars.associativity

  datatype type_structure =
      TYCON  of {Thy : string, Tyop : string, Kind : Kind.kind, Rank : int}
    | TYAPP  of type_structure * type_structure
    | TYUNIV of type_structure * type_structure
    | TYABST of type_structure * type_structure
    | TYVAR  of string * Kind.kind * int (* rank *)
    | PARAM  of int    * Kind.kind * int (* rank *)

  type grammar

  type special_info   = {lambda : string list,
                         forall : string list}
  val empty_grammar    : grammar
  val rules            : grammar -> (int * grammar_rule) list
  val abbreviations    : grammar -> (string,type_structure) Binarymap.dict
  val specials         : grammar -> special_info
  val fupdate_rules    : ((int * grammar_rule) list -> (int * grammar_rule) list) -> grammar -> grammar
  val fupdate_specials : (special_info -> special_info) -> grammar -> grammar
  val var_grammar      : grammar -> grammar

  val abb_dest_type : grammar -> Type.hol_type -> string * Type.hol_type list
  val disable_abbrev_printing : string -> grammar -> grammar

  val new_binary_tyop  : grammar
                          -> {precedence : int,
                              infix_form : string option,
                              opname : string,
                              associativity : HOLgrammars.associativity}
                          -> grammar

  val remove_binary_tyop : grammar -> string -> grammar
  (* removes by infix symbol, i.e. "+", not "sum" *)

  val new_tyop         : grammar -> string -> grammar
  val new_tybinder     : grammar -> string list -> grammar
  val new_abbreviation : grammar -> string * type_structure -> grammar
  val remove_abbreviation : grammar -> string -> grammar
  val num_params : type_structure -> int

  val merge_grammars   : grammar * grammar -> grammar

  val std_suffix_precedence : int
  val prettyprint_grammar   : Portable.ppstream -> grammar -> unit
  val initialise_typrinter
    : (grammar -> Portable.ppstream -> Type.hol_type -> unit) -> unit

end
