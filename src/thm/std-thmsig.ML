signature Thm =
sig

  include FinalThm where type tag = Tag.tag
                     and type hol_type = Type.hol_type
                     and type term = Term.term
end
