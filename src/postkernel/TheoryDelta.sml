structure TheoryDelta =
struct

 type thminfo = DB_dtype.thminfo
 datatype t =
   NewTheory of {oldseg: string, newseg: string}
 | ExportTheory of string
 | TheoryLoaded of string
 | NewConstant of KernelSig.kernelname
 | NewTypeOp of KernelSig.kernelname
 | DelConstant of KernelSig.kernelname
 | DelTypeOp of KernelSig.kernelname
 | NewBinding of string * (Thm.thm * thminfo)
 | UpdBinding of string * {thm:Thm.thm, old: thminfo, new:thminfo}
 | DelBinding of string

(* Events whose effect on a downstream "is this stored delta still
   up-to-date?" scan is wholly explained by KernelSig.retire_epoch.
   Listeners that only care about retire-state can skip a scan on such
   an event when the epoch is unchanged since their last scan. *)
fun retire_memoable (NewConstant _) = true
  | retire_memoable (NewTypeOp _) = true
  | retire_memoable (DelConstant _) = true
  | retire_memoable (DelTypeOp _) = true
  | retire_memoable _ = false

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
    | NewBinding (s,(_ (* th *), i)) =>
        "NewBinding(\"" ^ String.toString s ^ "\", " ^
        DB_dtype.thminfo_toString i ^ ")"
    | DelBinding s => sOp "DelBinding" s
    | UpdBinding (s, _) => sOp "UpdBinding" s
end (* local *)

end
