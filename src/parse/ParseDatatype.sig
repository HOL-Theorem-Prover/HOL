signature ParseDatatype =
sig


 datatype pretype = datatype ParseDatatype_dtype.pretype
 datatype datatypeForm = datatype ParseDatatype_dtype.datatypeForm
 type AST = ParseDatatype_dtype.AST
 type field = ParseDatatype_dtype.field
 type constructor = ParseDatatype_dtype.constructor
 val pretypeToType : pretype -> Type.hol_type

 val parse : type_grammar.grammar -> Type.hol_type Portable.quotation ->
             AST list

(*---------------------------------------------------------------------------
  Grammar we're parsing is:

      G            ::=  id "=" <form> (";" id "=" <form>)* ";"?
      form         ::=  <phrase> ( "|" <phrase> ) *  |  <record_defn>
      phrase       ::=  id  | id "of" <ptype> ( "=>" <ptype> ) *
      record_defn  ::=  "<|"  <idtype_pairs> ";"? "|>"
      idtype_pairs ::=  id ":" <type> | id : <type> ";" <idtype_pairs>
      ptype        ::=  <type> | "(" <type> ")"

  It had better be the case that => is not a type infix.  This is true of
  the standard HOL distribution.  In the event that => is an infix, this
  code will still work as long as the input puts the types in parentheses.
 ---------------------------------------------------------------------------*)

val hparse : type_grammar.grammar -> Type.hol_type Portable.quotation ->
             AST list

(* The grammar for hparse is:

   G        ::= id "=" <form> (";" id "=" <form>)* ";"?
   form     ::= "|"? <phrase> ( "|" <phrase> )* | <record_defn>
   phrase   ::= id <typarg>*
   typarg   ::= atomic-typ | "(" <type> ")"

  where record_defn is as above, and an atomic-typ is either a type variable,
  or a type-constant of arity 0, or one of the types being defined.
*)

val parse_listener : (AST list) Listener.t

end
