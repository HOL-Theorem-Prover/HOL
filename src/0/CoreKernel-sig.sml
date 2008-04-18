signature CoreKernel = sig
  structure Tag  : FinalTag
  structure Type : FinalType
  structure Term : FinalTerm        where type hol_type = Type.hol_type

  structure Thm  : Thm              where type hol_type = Type.hol_type
                                      and type term     = Term.term
                                      and type tag      = Tag.tag

  structure Theory : Theory         where type hol_type = Type.hol_type
                                      and type term     = Term.term
                                      and type thm      = Thm.thm

  structure TheoryPP : TheoryPP     where type hol_type = Type.hol_type
                                      and type thm      = Thm.thm

  structure Net : Net               where type term = Term.term

  structure Definition : Definition where type term = Term.term
                                      and type thm  = Thm.thm
end;
