(* ===================================================================== *)
(* FILE          : parse.sig                                             *)
(* DESCRIPTION   : Signature for the type and term parsers.              *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* ===================================================================== *)


signature Parse =
sig

 type 'a quotation = 'a Portable_General.frag list

  val parse0 : (int,Type.hol_type) Lib.istream 
                -> string -> Term.term list -> Parse_support.parse

  val Type : Type.hol_type quotation -> Type.hol_type
  val ==   : Type.hol_type quotation -> 'a -> Type.hol_type
  val type_parser : Type.hol_type quotation -> Type.hol_type

  val term_parser : Term.term quotation -> Term.term
  val Term : Term.term quotation -> Term.term
  val --   : Term.term quotation -> 'a -> Term.term
  val preterm_parser 
     : (int,Type.hol_type) Lib.istream 
        -> Term.term quotation 
          -> Preterm.preterm

  val string_to_type : string -> Type.hol_type
  val string_to_term : string -> Term.term
  val string_to_preterm 
    : (int,Type.hol_type) Lib.istream -> string -> Preterm.preterm

  val hidden : string -> bool
  val hide : string -> unit
  val reveal : string -> unit

  val typedTerm : Term.term quotation -> Type.hol_type -> Term.term
end;
