signature OpenTheoryCommon =
sig

datatype object
= ONum of int
| OName of string
| OList of object list
| OTypeOp of OpenTheoryMap.thy_tyop
| OType of Type.hol_type
| OConst of OpenTheoryMap.thy_const
| OVar of Term.term
| OTerm of Term.term
| OThm of Thm.thm

val object_compare : object * object -> order

val tyvar_to_ot   : string -> string
val tyvar_from_ot : string -> string
end
