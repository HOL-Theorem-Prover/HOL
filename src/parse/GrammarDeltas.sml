structure GrammarDeltas :> GrammarDeltas =
struct

open HolKernel term_grammar_dtype term_grammar
open LoadableThyData

val ERROR = mk_HOL_ERR "GrammarDeltas"
val tag = "GrammarDeltas"

fun delta_terms (d:user_delta) =
  case d of
      OVERLOAD_ON (s,t) => [t]
    | _ => []

val deltal_terms = List.foldl (fn (d, acc) => delta_terms d @ acc) []

val (toData, fromData) = LoadableThyData.new {
      thydataty = tag,
      merge = op@,
      terms = deltal_terms,
      read = (fn rtm => Coding.lift (Coding.many (user_delta_reader rtm))),
      write = (fn wtm => String.concat o map (user_delta_encode wtm))
}

fun thy_deltas {thyname} =
  case segment_data {thy=thyname,thydataty=tag} of
      NONE => []
    | SOME t => valOf (fromData t)
                handle Option => raise ERROR "thy_deltas"
                                       ("Bad encoding for "^thyname^"$"^tag)

fun userdelta_toString ud =
  case ud of
      OVERLOAD_ON (s, _) => "OVERLOAD_ON(" ^ Lib.mlquote s ^ ")"
    | _ => ""

fun record_delta d =
   write_data_update {thydataty = tag, data = toData [d]}

fun check_delta (d: user_delta) =
  case d of
      OVERLOAD_ON (_, t) => Term.uptodate_term t
    | _ => true

fun revise_data td =
  case segment_data {thy = current_theory(), thydataty = tag} of
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
                  set_theory_data {thydataty = tag, data = toData ok})
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
