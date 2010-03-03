signature parse_kind =
sig

  type ('a,'b) kindconstructors =
     {varkind : string locn.located -> 'a,
      kindop : (string locn.located * 'a list) -> 'a,
      qkindop : {Thy:string, Kindop:string, Locn:locn.locn, Args: 'a list} -> 'a,
      arity : (string locn.located * int) -> 'a,
      antiq : 'b -> 'a}

  val parse_kind :
    {varkind : string locn.located -> 'a,
     kindop : (string locn.located * 'a list) -> 'a,
     qkindop : {Thy:string, Kindop:string, Locn:locn.locn, Args: 'a list} -> 'a,
     arity : (string locn.located * int) -> 'a,
     antiq : 'b -> 'a} ->
    bool ->
    kind_grammar.grammar ->
    'b qbuf.qbuf -> 'a

  val kd_antiq      : Kind.kind -> Type.hol_type
  val dest_kd_antiq : Type.hol_type -> Kind.kind
  val is_kd_antiq   : Type.hol_type -> bool

  val ty_antiq      : Type.hol_type -> Term.term
  val dest_ty_antiq : Term.term -> Type.hol_type
  val is_ty_antiq   : Term.term -> bool

  val kd_ty_antiq      : Kind.kind -> Term.term
  val dest_kd_ty_antiq : Term.term -> Kind.kind
  val is_kd_ty_antiq   : Term.term -> bool

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
