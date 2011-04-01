signature rank_tokens = sig

  datatype 'a rank_token
      = RankNumeral of string
      | AQ of 'a
      | Error of 'a base_tokens.base_token

  val ranktok_of : 'a qbuf.qbuf -> ((unit -> unit) * 'a rank_token locn.located)

  val token_string : 'a rank_token -> string
  val dest_aq : 'a rank_token -> 'a

  val is_rankaq : 'a rank_token -> bool

end
