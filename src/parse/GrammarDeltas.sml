structure GrammarDeltas :> GrammarDeltas =
struct

open HolKernel type_grammar_dtype term_grammar_dtype term_grammar
open HOLgrammars LoadableThyData

val ERROR = mk_HOL_ERR "GrammarDeltas"
val tmtag = "TermGrammarDeltas"
val tytag = "TypeGrammarDeltas"

fun ty_as_term ty = mk_var("x", ty)

fun tydelta_terms (d:type_grammar.delta) =
  case d of
      TYABBREV (_, ty) => [ty_as_term ty]
    | _ => []

val tydeltal_terms = List.foldl (fn (d,acc) => tydelta_terms d @ acc) []

fun tydelta_reader readtm =
  let
    open Coding
    infix || >> >*
    fun new_infix (((nm,pnm),assoc),prec) =
      NEW_INFIX {Name = nm, ParseName = pnm, Assoc = assoc, Prec = prec}
    fun tyabbrev (kid, tm) = TYABBREV (kid, type_of tm)
  in
    (literal "NTY" >> Coding.map NEW_TYPE KernelNameData.reader) ||
    (literal "NIX" >>
     Coding.map new_infix (StringData.reader >* StringData.reader >*
                           assoc_reader >* IntData.reader)) ||
    (literal "TYA" >>
     Coding.map tyabbrev
       (KernelNameData.reader >* Coding.map readtm StringData.reader)) ||
    (literal "DTYP" >> Coding.map DISABLE_TYPRINT StringData.reader) ||
    (literal "RKA" >> Coding.map RM_KNM_TYABBREV KernelNameData.reader) ||
    (literal "RTY" >> Coding.map RM_TYABBREV StringData.reader)
  end

fun tydelta_encode wtm tyd =
  let
    open Coding optmonad
  in
    case tyd of
        NEW_TYPE kid => "NTY" ^ KernelNameData.encode kid
      | NEW_INFIX{Name,ParseName,Assoc,Prec} =>
          "NIX" ^ StringData.encode Name ^ StringData.encode ParseName ^
          assoc_encode Assoc ^ IntData.encode Prec
      | TYABBREV (kid, ty) =>
          "TYA" ^ KernelNameData.encode kid ^
          StringData.encode (wtm (ty_as_term ty))
      | DISABLE_TYPRINT s => "DTYP" ^ StringData.encode s
      | RM_KNM_TYABBREV kid => "RKA" ^ KernelNameData.encode kid
      | RM_TYABBREV s => "RTY" ^ StringData.encode s
  end

val (tyd_toData, tyd_fromData) = LoadableThyData.new {
      thydataty = tytag,
      merge = op@,
      terms = tydeltal_terms,
      read = (fn rtm => Coding.lift (Coding.many (tydelta_reader rtm))),
      write = (fn wtm => String.concat o map (tydelta_encode wtm))
    }

fun record_tydelta d =
   write_data_update {thydataty = tytag, data = tyd_toData [d]}

fun tmdelta_terms (d:user_delta) =
  case d of
      OVERLOAD_ON (_,t) => [t]
    | IOVERLOAD_ON (_, t) => [t]
    | GRMOVMAP (_, t) => [t]
    | ADD_UPRINTER {pattern,...} => [pattern]
    | _ => []

val tmdeltal_terms = List.foldl (fn (d, acc) => tmdelta_terms d @ acc) []

val (toData, fromData) = LoadableThyData.new {
      thydataty = tmtag,
      merge = op@,
      terms = tmdeltal_terms,
      read = (fn rtm => Coding.lift (Coding.many (user_delta_reader rtm))),
      write = (fn wtm => String.concat o map (user_delta_encode wtm))
}

fun thy_deltas {thyname} =
  let
    val tmds =
        case segment_data {thy=thyname,thydataty=tmtag} of
            NONE => []
          | SOME t => valOf (fromData t)
                      handle Option => raise ERROR "thy_deltas"
                                             ("Bad encoding for "^thyname^"$"^
                                              tmtag)
    val tyds =
        case segment_data {thy = thyname, thydataty = tytag} of
            NONE => []
          | SOME t => valOf (tyd_fromData t)
                      handle Option => raise ERROR "thy_deltas"
                                             ("Bad encoding for "^thyname^"$"^
                                              tytag)
  in
    (tyds, tmds)
  end


fun userdelta_toString ud =
  case ud of
      OVERLOAD_ON (s, _) => "overload_on(" ^ Lib.mlquote s ^ ")"
    | CLR_OVL s => "clear_overloads_on(" ^ Lib.mlquote s ^ ")"
    | _ => ""

fun record_tmdelta d =
   write_data_update {thydataty = tmtag, data = toData [d]}

fun check_delta (d: user_delta) =
  case d of
      OVERLOAD_ON (_, t) => Term.uptodate_term t
    | IOVERLOAD_ON (_, t) => Term.uptodate_term t
    | GRMOVMAP(_, t) => Term.uptodate_term t
    | MOVE_OVLPOSN {skid = (_, kid), ...} => can prim_mk_const kid
    | RMOVMAP (_, kid) => can prim_mk_const kid
    | _ => true

fun revise_data td =
  case segment_data {thy = current_theory(), thydataty = tmtag} of
      NONE => ()
    | SOME d =>
      let
        val deltas = valOf (fromData d)
        val (ok,notok) = Lib.partition check_delta deltas
      in
        case notok of
            [] => ()
          | _ => (HOL_WARNING "GrammarDeltas" "revise_data"
                              ("\n  Grammar-deltas:\n    " ^
                               String.concatWith ", "
                                                 (map userdelta_toString notok)^
                               "\n  invalidated by " ^ TheoryDelta.toString td);
                  set_theory_data {thydataty = tmtag, data = toData ok})
      end

fun hook td =
  let
    open TheoryDelta
  in
    case td of
        TheoryLoaded _ => () (* should ultimately change grammars *)
      | DelConstant _ => revise_data td
      | DelTypeOp _ => revise_data td
      | NewConstant _ => revise_data td
      | NewTypeOp _ => revise_data td
      | _ => ()
  end

val _ = register_hook ("GrammarDeltas", hook)

end
