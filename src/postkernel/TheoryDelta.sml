structure TheoryDelta =
struct

 datatype t =
   NewTheory of {oldseg: string, newseg: string}
 | ExportTheory of string
 | TheoryLoaded of string
 | NewConstant of KernelSig.kernelname
 | NewTypeOp of KernelSig.kernelname
 | DelConstant of KernelSig.kernelname
 | DelTypeOp of KernelSig.kernelname
 | DelBinding of string

local
  fun ksOp opnm ks = opnm ^ "(" ^ KernelSig.name_toString ks ^ ")"
  fun sOp opnm s = opnm ^ "(" ^ s ^ ")"
in
fun toString t =
    case t of
      NewTheory {oldseg,newseg} =>
      String.concat ["NewTheory{oldseg = ", Lib.quote oldseg, ", ",
                     "newseg = ", Lib.quote newseg, "}"]
    | ExportTheory s => sOp "ExportTheory" s
    | TheoryLoaded s => sOp "TheoryLoaded" s
    | NewConstant n => ksOp "NewConstant" n
    | NewTypeOp n => ksOp "NewTypeOp" n
    | DelConstant n => ksOp "DelConstant" n
    | DelTypeOp n => ksOp "DelTypeOp" n
    | DelBinding s => sOp "DelBinding" s
end (* local *)

end
