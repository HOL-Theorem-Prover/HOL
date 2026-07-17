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

(* Consumers gate their scans on retire_epoch. The two predicates
   below carve out which events they can trust that gate on.

   retire_memoable: events whose scan-need is entirely a function of
   retire_epoch.  ThmSetData uses this — its NewBinding hook
   (neqbinding) does real work on additive events, so those aren't
   captured here.

   retire_captured: additionally includes NewBinding / NewTheory,
   whose only effect on a pure retire-state predicate is additive.
   DelBinding retires a DB entry without bumping retire_epoch and is
   never captured; UpdBinding / ExportTheory are excluded
   conservatively. *)
fun retire_memoable (NewConstant _) = true
  | retire_memoable (NewTypeOp _) = true
  | retire_memoable (DelConstant _) = true
  | retire_memoable (DelTypeOp _) = true
  | retire_memoable _ = false

fun retire_captured (NewBinding _) = true
  | retire_captured (NewTheory _) = true
  | retire_captured e = retire_memoable e

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
