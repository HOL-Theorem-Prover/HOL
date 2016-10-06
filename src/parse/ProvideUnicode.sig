signature ProvideUnicode =
sig

  type term = Term.term
  type grammar = term_grammar.grammar
  type urule = {u:string list, term_name : string,
                newrule : term_grammar.grule,
                oldtok : string option}

  datatype stored_data =
           RuleUpdate of urule
         | OverloadUpdate of { u : string, ts : term list }
  val stored_data : unit -> stored_data list

  val record_data : stored_data -> unit

  (* functions for manipulating use of Unicode versions of constants *)

  (* bool switch on following 5 functions is whether or not Unicode is on.
     Need to make these calls even when it's not on so that the good stuff
     can be enabled when the flag is turned on. *)
  val temp_uoverload_on : bool -> string * term -> grammar -> grammar
  val temp_uadd_rule : bool -> urule -> grammar -> grammar

  val uoverload_on : bool -> string * term -> grammar -> grammar
  val uadd_rule : bool -> urule -> grammar -> grammar
  val apply_thydata : bool -> string -> grammar -> grammar

  val mk_unicode_version : {u:string,tmnm:string} -> grammar ->
                           stored_data * term_grammar.user_delta list


  val enable_all : grammar -> grammar
  val disable_all : grammar -> grammar


  datatype ThyUpdateInfo = UV of {u:string,tmnm:string}
                         | RULE of urule
                         | OVL of string * term

  val record_updateinfo : ThyUpdateInfo -> unit

end
