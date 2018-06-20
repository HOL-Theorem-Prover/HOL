structure Absyn_dtype =
struct

  datatype vstruct
       = VAQ    of locn.locn * Term.term
       | VIDENT of locn.locn * string
       | VPAIR  of locn.locn * vstruct * vstruct
       | VTYPED of locn.locn * vstruct * Pretype.pretype

   datatype absyn
       = AQ     of locn.locn * Term.term
       | IDENT  of locn.locn * string
       | QIDENT of locn.locn * string * string
       | APP    of locn.locn * absyn * absyn
       | LAM    of locn.locn * vstruct * absyn
       | TYPED  of locn.locn * absyn * Pretype.pretype

end
