signature ProvideUnicode =
sig

  val mk_unicode_version : {u:string,tmnm:string} -> term_grammar.grammar ->
                           term_grammar.user_delta list
end
