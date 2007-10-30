signature kind_grammar =
sig

(* HOL-Omega concrete syntax (suggestive):

Kind is the root nonterminal.

Kind   ::= '*' | Kind '=>' Kind | 'ar' Numeral | '(' Kind ')'

*)

  datatype grammar_rule
    = NONFIX
    | INFIX of {opname : string, parse_string : string} list *
                HOLgrammars.associativity
    | PREFIX of string list

  datatype kind_structure
    = KINDOP of {Thy : string, Kindop : string, Args : kind_structure list}

  type grammar

  val empty_grammar    : grammar
  val rules            : grammar -> (int * grammar_rule) list
(*
  val abbreviations    : grammar -> (string,kind_structure) Binarymap.dict

  val abb_dest_kind : grammar -> Kind.kind -> string * Kind.kind list
  val disable_abbrev_printing : string -> grammar -> grammar
*)

  val new_binary_kindop : grammar
                          -> {precedence : int,
                              infix_form : string option,
                              opname : string,
                              associativity : HOLgrammars.associativity}
                          -> grammar

  val remove_binary_kindop : grammar -> string -> grammar
  (* removes by infix symbol, i.e. "+", not "sum" *)

  val new_kindop       : grammar -> string -> grammar
(*
  val new_abbreviation : grammar -> string * kind_structure -> grammar
  val remove_abbreviation : grammar -> string -> grammar
*)
  val merge_grammars   : grammar * grammar -> grammar

  val std_prefix_precedence : int
  val prettyprint_grammar   : Portable.ppstream -> grammar -> unit
  val initialise_kindprinter
    : (grammar -> Portable.ppstream -> Kind.kind -> unit) -> unit

end
