signature ParseDatatype =
sig

  datatype pretype =
    dVartype of string | dTyop of (string * pretype list) |
    dAQ of Type.hol_type

  val pretypeToType : pretype -> Type.hol_type
  type recordtype_info = (string * pretype) list

  datatype datatypeForm =
    WithConstructors of (string * pretype list) list |
    RecordType of recordtype_info
  type datatypeAST = string (* type name *) * datatypeForm

   val parse : Type.hol_type frag list -> datatypeAST list

(* grammar we're parsing is:
    G ::=              id "=" <form>
    form ::=           <phrase> ( "|" <phrase> ) *  |  <record_defn>
    phrase ::=         id  | id "of" <ptype> ( "=>" <ptype> ) *
    record_defn ::=    "<|"  <idtype_pairs> "|>"
    idtype_pairs ::=   id ":=" <type> | id := <type> "," <idtype_pairs>
    ptype ::=          <type> | "(" <type> ")"
 *
 * It had better be the case that => is not a type infix.  This is true of
 * the standard HOL distribution.  In the event that => is an infix, this
 * code will still work as long as the input puts the types in parentheses.
 *)


end;
