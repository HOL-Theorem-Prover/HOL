signature ParseDatatype =
sig

 type hol_type = Type.hol_type
 type tyname   = string
 type quote    = hol_type frag list

  datatype pretype 
      = dVartype of string 
      | dTyop    of string * pretype list
      | dAQ      of Type.hol_type

  val pretypeToType : pretype -> hol_type

  type field       = string * pretype
  type constructor = string * pretype list

  datatype datatypeForm
      = Constructors of constructor list
      | Record of field list

  type AST = tyname * datatypeForm

  val parse : quote -> AST list

(*---------------------------------------------------------------------------
  grammar we're parsing is: 

    G ::=              id "=" <form>
    form ::=           <phrase> ( "|" <phrase> ) *  |  <record_defn>
    phrase ::=         id  | id "of" <ptype> ( "=>" <ptype> ) *
    record_defn ::=    "<|"  <idtype_pairs> "|>"
    idtype_pairs ::=   id ":" <type> | id : <type> ";" <idtype_pairs>
    ptype ::=          <type> | "(" <type> ")"
 
  It had better be the case that => is not a type infix.  This is true of
  the standard HOL distribution.  In the event that => is an infix, this
  code will still work as long as the input puts the types in parentheses.
 ---------------------------------------------------------------------------*)


end;
