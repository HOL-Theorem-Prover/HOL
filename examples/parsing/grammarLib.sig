signature grammarLib =
sig

  include Abbrev
  datatype stringt = S of string | TM of term
  datatype sym = NT of string | TOK of stringt
  type t = (string * sym list list) list

  val grammar : term frag list -> t
(*   val mk_grammar_t : (string -> term) -> term quotation -> term *)


end
