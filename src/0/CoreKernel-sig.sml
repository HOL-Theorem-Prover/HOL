signature CoreKernel = sig
  structure Tag  : FinalTag
  structure Rank : FinalRank
  structure Kind : FinalKind        where type rank     = Rank.rank
  structure Type : FinalType        where type kind     = Kind.kind
                                      and type rank     = Rank.rank
  structure Term : FinalTerm        where type hol_type = Type.hol_type
                                      and type kind     = Kind.kind
                                      and type rank     = Rank.rank

  structure Thm  : Thm              where type kind     = Kind.kind
                                      and type rank     = Rank.rank
                                      and type hol_type = Type.hol_type
                                      and type term     = Term.term
                                      and type tag      = Tag.tag

  structure Theory : Theory         where type kind     = Kind.kind
                                      and type hol_type = Type.hol_type
                                      and type term     = Term.term
                                      and type thm      = Thm.thm

  structure TheoryPP : TheoryPP     where type kind     = Kind.kind
                                      and type hol_type = Type.hol_type
                                      and type thm      = Thm.thm

  structure Net : Net               where type term = Term.term

  structure Definition : Definition where type term = Term.term
                                      and type thm  = Thm.thm
end;
