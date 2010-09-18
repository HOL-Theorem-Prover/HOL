signature ProvideUnicode =
sig

  type term = Term.term
  type grammar = term_grammar.grammar
  type urule = {u:string list, term_name : string,
                newrule : term_grammar.user_delta,
                oldtok : string option}

  datatype stored_data =
           RuleUpdate of urule
         | OverloadUpdate of { u : string, ts : term list }
  val stored_data : unit -> stored_data list

  (* functions for manipulating use of Unicode versions of constants *)

  (* bool switch on following 7 functions is whether or not Unicode is on.
     Need to make these calls even when it's not on so that the good stuff
     can be enabled when the flag is turned on. *)
  val temp_unicode_version : bool -> {u:string,tmnm:string} ->
                             grammar -> grammar
  val temp_uoverload_on : bool -> string * term -> grammar -> grammar
  val temp_uadd_rule : bool -> urule -> grammar -> grammar

  val unicode_version : bool -> {u:string,tmnm:string} -> grammar -> grammar
  val uoverload_on : bool -> string * term -> grammar -> grammar
  val uadd_rule : bool -> urule -> grammar -> grammar
  val apply_thydata : bool -> string -> grammar -> grammar

  val enable_all : grammar -> grammar
  val disable_all : grammar -> grammar


datatype ThyUpdateInfo = UV of {u:string,tmnm:string}
                       | RULE of urule
                       | OVL of string * term
val encode : ThyUpdateInfo -> string
val decode : string -> ThyUpdateInfo option
val reader : ThyUpdateInfo Coding.reader


end

