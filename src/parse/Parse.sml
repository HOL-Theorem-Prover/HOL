(* ===================================================================== *)
(* FILE          : parse.sml                                             *)
(* DESCRIPTION   : Implements parsing of HOL terms and types.            *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* DATE          : Dec. 9, 1998                                          *)
(* ===================================================================== *)


structure Parse :> Parse =
struct

open Portable_General;
type 'a quotation = 'a frag list

fun PARSE_ERR func mesg = 
 Exception.HOL_ERR{origin_structure = "Parse",
              origin_function = func,
              message = mesg}

fun error (s,_,_) = raise PARSE_ERR "Parsing error" s

fun format [] ol ml = (ol, rev ml) 
  | format (ANTIQUOTE  x::rst) ol ml = format rst (ol^"^") (x::ml)
  | format (QUOTE s::rst) ol ml = format rst (ol^s) ml;


local val fst_time = ref true
in fun parse0 tyvars s aqs =
   let val _  = fst_time := true
       fun give_s _ = if !fst_time then (fst_time := false ; s) else ""
       val lexer = HolParser.makeLexer give_s (ref aqs)
   in Lib.fst(HolParser.parse(0,lexer,error,tyvars))
   end
end;

fun pstring tyvars = Lib.C (parse0 tyvars) [];

fun pquote tyvars ol_frag_list =
   let val (s,antiq_list) = format ol_frag_list "" []
   in parse0 tyvars s antiq_list
   end; 

(*---------------------------------------------------------------------------*
 * Parsing to preterms.                                                      *
 *---------------------------------------------------------------------------*)
fun preterm_parser tyvars frag_list =
  (Globals.in_type_spec := NONE;
   case (pquote tyvars frag_list)
     of (Parse_support.PTM ptm) => ptm
      | _ => raise PARSE_ERR "preterm_parser" "Not a preterm.");

fun string_to_preterm tyvars s =
  (Globals.in_type_spec := NONE;
   case (pstring tyvars s)
     of (Parse_support.PTM ptm) => ptm
      | _ => raise PARSE_ERR "string_to_preterm" "Not a preterm.");

(*---------------------------------------------------------------------------*
 * Parsing to terms.                                                         *
 *---------------------------------------------------------------------------*)
fun term_parser frag_list =
  let val _ = Globals.in_type_spec := NONE;
      val tyvars = Type.fresh_tyvar_stream()
  in case (pquote tyvars frag_list)
       of (Parse_support.PTM ptm) => Preterm.typecheck tyvars ptm
        | _ => raise PARSE_ERR "term_parser" "Not a term." 
  end;

fun string_to_term s =
  let val _ = Globals.in_type_spec := NONE;
      val tyvars = Type.fresh_tyvar_stream()
  in case (pstring tyvars s)
     of (Parse_support.PTM ptm) => Preterm.typecheck tyvars ptm
      | _ => raise PARSE_ERR "string_to_term" "Not a term."
  end;

val Term = Lib.try term_parser;
fun -- frag_list _ = Lib.try term_parser frag_list;

(*---------------------------------------------------------------------------*
 * Parsing to types                                                          *
 *---------------------------------------------------------------------------*)
fun type_parser q = Pretype.pretype2type Pretype.name_of (Pretype.parse q);
fun string_to_type s = type_parser [QUOTE s];
val Type = Lib.try type_parser;
fun == frag_list _ = Lib.try type_parser frag_list;


val hidden = Parse_support.hidden
val hide   = Parse_support.hide
val reveal = Parse_support.reveal


(* constrain parsed term to have a given type *)
fun typedTerm qtm ty = 
   let fun trail s = [QUOTE (s^"):"), ANTIQUOTE(Term.ty_antiq ty), QUOTE""]
   in
   Term (case (Lib.front_last qtm)
        of ([],QUOTE s) => trail ("("^s)
         | (QUOTE s::rst, QUOTE s') => (QUOTE ("("^s)::rst) @ trail s'
         | _ => raise PARSE_ERR"typedTerm" "badly formed quotation")
   end;

end; (* PARSE *)
