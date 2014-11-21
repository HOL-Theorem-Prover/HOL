signature ParseDatatype =
sig

 datatype pretype =
   dVartype of string
 | dTyop of {Tyop : string, Thy : string option, Args : pretype list}
 | dAQ of Type.hol_type

 val pretypeToType : pretype -> Type.hol_type

 type field       = string * pretype
 type constructor = string * pretype list

 datatype datatypeForm =
   Constructors of constructor list
 | Record of field list

 type AST = string * datatypeForm

 val parse : Type.hol_type Portable.quotation -> AST list

(*---------------------------------------------------------------------------
  Grammar we're parsing is:

      G            ::=  id "=" <form> (";" id "=" <form>)*
      form         ::=  <phrase> ( "|" <phrase> ) *  |  <record_defn>
      phrase       ::=  id  | id "of" <ptype> ( "=>" <ptype> ) *
      record_defn  ::=  "<|"  <idtype_pairs> "|>"
      idtype_pairs ::=  id ":" <type> | id : <type> ";" <idtype_pairs>
      ptype        ::=  <type> | "(" <type> ")"

  It had better be the case that => is not a type infix.  This is true of
  the standard HOL distribution.  In the event that => is an infix, this
  code will still work as long as the input puts the types in parentheses.
 ---------------------------------------------------------------------------*)

val hparse : Type.hol_type Portable.quotation -> AST list

(* The grammar for hparse is:

   G        ::= id "=" <form> (";" id "=" <form>)*
   form     ::= "|"? <phrase> ( "|" <phrase> )* | <record_defn>
   phrase   ::= id <typarg>*
   typarg   ::= atomic-typ | "(" <type> ")"

  where record_defn is as above, and an atomic-typ is either a type variable,
  or a type-constant of arity 0, or one of the types being defined.
*)

end
