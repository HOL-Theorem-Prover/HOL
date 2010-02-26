signature type_grammar =
sig

  datatype grammar_rule
    = SUFFIX of string list
    | ARRAY_SFX
    | INFIX of {opname : string, parse_string : string} list *
                HOLgrammars.associativity

  datatype type_structure
    = TYOP of {Thy : string, Tyop : string, Args : type_structure list}
    | PARAM of int

  type grammar

  val empty_grammar    : grammar
  val min_grammar      : grammar
  val rules            : grammar -> (int * grammar_rule) list
  val abbreviations    : grammar -> (string,type_structure) Binarymap.dict

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
  val new_abbreviation : grammar -> string * type_structure -> grammar
  val remove_abbreviation : grammar -> string -> grammar
  val num_params : type_structure -> int

  val merge_grammars   : grammar * grammar -> grammar

  val std_suffix_precedence : int
  val prettyprint_grammar   : Portable.ppstream -> grammar -> unit
  val initialise_typrinter
    : (grammar -> Portable.ppstream -> Type.hol_type -> unit) -> unit

end
