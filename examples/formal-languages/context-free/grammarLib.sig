signature grammarLib =
sig

  include Abbrev
  datatype stringt = S of string | TMnm of string
  datatype sym = NT of string | TOK of stringt
  datatype clause = Syms of sym list | TmAQ of term
  type t = (string * clause list) list

  val grammar : term frag list -> t

  val mk_grammar_def : {tokmap : string -> term, tokty : hol_type,
                        nt_tyname : string, start : string, gname : string,
                        mkntname : string -> string} ->
                       term quotation -> thm

end
