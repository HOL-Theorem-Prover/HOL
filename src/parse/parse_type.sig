signature parse_type = 
sig
  type 'a token = 'a type_tokens.type_token
  datatype grammar_rule =
    SUFFIX of string list
  | INFIX of {opname : string, parse_string : string} list *
             HOLgrammars.associativity

  type grammar
  val rules : grammar -> (int * grammar_rule) list

  val parse_type :
    {vartype : string -> 'a,
     tyop : (string * 'a list) -> 'a,
     antiq : 'b -> 'a} ->
    bool ->
    grammar ->
    ('a, 'b frag) monadic_parse.Parser

    (* The record of functions specify how to deal with the need to
       construct variable types, type operators and antiquotations

       The boolean argument specifies whether or not arbitrary type names
       should be accepted as suffixes.  With this set to true, the parser
       will not cavil at "'a foo", for arbitrary identifier foo.  With it
       false, it will only permit suffixes that are present in the grammar.

       The parameter is set to true for parsing datatype definitions, where
       it is useful to be able to mention types that don't actually exist
       yet. *)
  val empty_grammar : grammar

  val new_binary_tyop :
    grammar -> {precedence : int,
                infix_form : string option,
                opname : string,
                associativity : HOLgrammars.associativity} -> grammar
  val new_tyop : grammar -> string -> grammar

  val std_suffix_precedence : int

  val merge_grammars : grammar * grammar -> grammar

end
