local
  open monadic_parse HOLgrammars
  type 'a token = 'a type_tokens.type_token
in

  datatype grammar_rule =
    SUFFIX of string list
  | INFIX of {opname : string, parse_string : string} list * associativity

  type grammar
  val rules : grammar -> (int * grammar_rule) list

  datatype 'a pretype =
    pVartype of string | pType of (string * 'a pretype list) | pAQ of 'a

  val parse_type : bool -> grammar -> (''a pretype, ''a frag) Parser
    (* The boolean argument specifies whether or not arbitrary type names
       should be accepted as suffixes.  With this set to true, the parser
       will not cavil at "'a foo", for arbitrary identifier foo.  With it
       false, it will only permit suffixes that are present in the grammar.

       The parameter is set to true for parsing datatype definitions, where
       it is useful to be able to mention types that don't actually exist
       yet. *)
  val empty_grammar : grammar

  val new_binary_tyop : grammar -> {precedence : int,
                                    infix_form : string option,
                                    opname : string,
                                    associativity : associativity} -> grammar
  val new_tyop : grammar -> string -> grammar

  val std_suffix_precedence : int

end

