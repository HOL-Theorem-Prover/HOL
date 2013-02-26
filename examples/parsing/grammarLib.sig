signature grammarLib =
sig

  include Abbrev
  datatype stringt = S of string | TMnm of string | TM of term
  datatype sym = NT of string | TOK of stringt
  type t = (string * sym list list) list

  val grammar : term frag list -> t

  val mk_grammar_def : {tokmap : string -> term, tokty : hol_type,
                        nt_tyname : string, start : string, gname : string,
                        mkntname : string -> string} ->
                       term quotation -> thm

end
