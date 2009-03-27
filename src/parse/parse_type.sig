signature parse_type =
sig

  val parse_type :
    {vartype : (string * Prekind.prekind * Prerank.prerank) locn.located -> 'a,
     tyop : (string locn.located * 'a list) -> 'a,
     qtyop : {Thy:string, Tyop:string, Locn:locn.locn, Args: 'a list} -> 'a,
     antiq : 'b -> 'a,
     kindcast : {Ty: 'a, Kind:Prekind.prekind, Locn:locn.locn} -> 'a,
     rankcast : {Ty: 'a, Rank:Prerank.prerank, Locn:locn.locn} -> 'a,
     tycon  : {Thy:string, Tyop:string, Kind:Prekind.prekind, Rank:Prerank.prerank, Locn:locn.locn} -> 'a,
     tyapp  : ('a * 'a) -> 'a,
     tyuniv : ('a * 'a) -> 'a,
     tyabs  : ('a * 'a) -> 'a,
     kindparser : 'b qbuf.qbuf -> Prekind.prekind} ->
    bool ->
    type_grammar.grammar ->
    'b qbuf.qbuf -> 'a

    (* The record of functions specify how to deal with the need to
       construct variable types, type operators and antiquotations

       The boolean argument specifies whether or not arbitrary type names
       should be accepted as suffixes.  With this set to true, the parser
       will not cavil at "'a foo", for arbitrary identifier foo.  With it
       false, it will only permit suffixes that are present in the grammar.

       The parameter is set to true for parsing datatype definitions, where
       it is useful to be able to mention types that don't actually exist
       yet. *)

end
