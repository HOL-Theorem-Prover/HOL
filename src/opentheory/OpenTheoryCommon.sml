structure OpenTheoryCommon :> OpenTheoryCommon = struct

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

val thm_compare = Lib.lex_cmp
  (Term.compare, Lib.list_compare Term.compare)
  (Thm.concl   , HOLset.listItems o Thm.hypset)

val object_compare = let
fun c (ONum    x1, ONum    x2) = Int.compare                (x1,x2)
  | c (ONum     _,          _) = LESS
  | c (         _, ONum     _) = GREATER
  | c (OName   x1, OName   x2) = String.compare             (x1,x2)
  | c (OName    _,          _) = LESS
  | c (         _, OName    _) = GREATER
  | c (OList   x1, OList   x2) = Lib.list_compare c         (x1,x2)
  | c (OList    _,          _) = LESS
  | c (         _, OList    _) = GREATER
  | c (OTypeOp x1, OTypeOp x2) = OpenTheoryMap.thy_tyop_cmp (x1,x2)
  | c (OTypeOp  _,          _) = LESS
  | c (         _, OTypeOp  _) = GREATER
  | c (OType   x1, OType   x2) = Type.compare               (x1,x2)
  | c (OType    _,          _) = LESS
  | c (         _, OType    _) = GREATER
  | c (OConst  x1, OConst  x2) = OpenTheoryMap.thy_const_cmp(x1,x2)
  | c (OConst   _,          _) = LESS
  | c (         _, OConst   _) = GREATER
  | c (OVar    x1, OVar    x2) = Term.compare               (x1,x2)
  | c (OVar     _,          _) = LESS
  | c (         _, OVar     _) = GREATER
  | c (OTerm   x1, OTerm   x2) = Term.compare               (x1,x2)
  | c (OTerm    _,          _) = LESS
  | c (         _, OTerm    _) = GREATER
  | c (OThm    x1, OThm    x2) = thm_compare                (x1,x2)
in c end

local open Thm Drule in
  fun DEDUCT_ANTISYM th1 th2 =
    IMP_ANTISYM_RULE
      (DISCH (concl th2) th1)
      (DISCH (concl th1) th2)
end

end
