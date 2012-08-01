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

local
  fun ksOp opnm ks = opnm ^ "(" ^ KernelSig.name_toString ks ^ ")"
in
fun toString t =
    case t of
      NewTheory {oldseg,newseg} =>
      String.concat ["NewTheory{oldseg = ", Lib.quote oldseg, ", ",
                     "newseg = ", Lib.quote newseg, "}"]
    | ExportTheory s => "ExportTheory(" ^ s ^ ")"
    | TheoryLoaded s => "TheoryLoaded(" ^ s ^ ")"
    | NewConstant n => ksOp "NewConstant" n
    | NewTypeOp n => ksOp "NewTypeOp" n
    | DelConstant n => ksOp "DelConstant" n
    | DelTypeOp n => ksOp "DelTypeOp" n
end (* local *)

end
