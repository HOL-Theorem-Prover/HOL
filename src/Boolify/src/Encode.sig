(* ========================================================================= *)
(* AUTOMATIC GENERATION OF ENCODING FUNCTIONS FOR DATATYPES.                 *)
(* Created by Joe Hurd, July 2002                                            *)
(* Basically the same as Konrad Slind's code to generate size functions      *)
(* ========================================================================= *)

signature Encode =
sig

  include Abbrev
  type tyinfo = TypeBasePure.tyinfo

  val define_encode :
    thm ->
      TypeBasePure.typeBase ->
        {const_tyopl: (term * (string * string)) list, def: thm} option

  val define_and_add_encode : tyinfo -> tyinfo

end
