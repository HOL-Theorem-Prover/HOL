signature CoreKernel = sig
  structure Tag  : FinalTag
  structure Type : FinalType
  structure Term : FinalTerm        where type hol_type = Type.hol_type

  structure Thm  : FinalThm         where type hol_type = Type.hol_type
                                      and type term     = Term.term
                                      and type tag      = Tag.tag

  structure Net : Net               where type term = Term.term

end;
