signature Thm =
sig

  include FinalThm where type hol_type = Type.hol_type
                     and type term = Term.term
                     and type tag = Tag.tag

end
