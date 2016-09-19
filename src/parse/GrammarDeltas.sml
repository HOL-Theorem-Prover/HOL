structure GrammarDeltas :> GrammarDeltas =
struct

open HolKernel term_grammar_dtype term_grammar

val ERROR = mk_HOL_ERR "GrammarDeltas"
val tag = "GrammarDeltas"

fun delta_terms (d:user_delta) = []

val deltal_terms = List.foldl (fn (d, acc) => delta_terms d @ acc) []

val (toData, fromData) = LoadableThyData.new {
      thydataty = tag,
      merge = op@,
      terms = deltal_terms,
      read = K (Coding.lift (Coding.many user_delta_reader)),
      write = K (String.concat o map user_delta_encode)
}

fun thy_deltas {thyname} =
  case LoadableThyData.segment_data {thy=thyname,thydataty=tag} of
      NONE => []
    | SOME t => valOf (fromData t)
                handle Option => raise ERROR "thy_deltas"
                                       ("Bad encoding for "^thyname^"$"^tag)

fun record_delta d =
  LoadableThyData.write_data_update {thydataty = tag, data = toData [d]}

end
