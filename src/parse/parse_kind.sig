signature parse_kind =
sig

  val parse_kind :
    {varkind : string locn.located -> 'a,
     kindop : (string locn.located * 'a list) -> 'a,
     qkindop : {Thy:string, Kindop:string, Locn:locn.locn, Args: 'a list} -> 'a,
     arity : (string locn.located * int) -> 'a,
     antiq : 'b -> 'a} ->
    bool ->
    kind_grammar.grammar ->
    'b qbuf.qbuf -> 'a

    (* The record of functions specify how to deal with the need to
       construct variable kinds, kind operators and antiquotations

       The boolean argument specifies whether or not arbitrary kind names
       should be accepted as prefixes.  With this set to true, the parser
       will not cavil at "foo <kind>", for arbitrary identifier foo.  With it
       false, it will only permit prefixes that are present in the grammar.

       The parameter is set to true for parsing new kind definitions, where
       it is useful to be able to mention kinds that don't actually exist
       yet. *)

end
