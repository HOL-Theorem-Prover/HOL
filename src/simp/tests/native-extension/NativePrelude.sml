(* Shared by the native-extension units.  The ordinary modules stay
   reachable under Ordinary* names, and the familiar names are rebound to
   the extension engine. *)
structure NativePrelude =
struct

(* Explicit imports for Holdep before the local aliases shadow them. *)
open simpLib pureSimps boolSimps congLib Traverse
     simpExtLib congExtLib TraverseExt

(* Interleaved cutover: extension callers use independently sealed sets.
   Keep the ordinary modules available for the baseline-only pins below. *)
structure OrdinarySimp = simpLib
structure OrdinaryPure = pureSimps
structure OrdinaryBool = boolSimps
structure OrdinaryCong = congLib
structure OrdinaryTraverse = Traverse
structure Traverse = TraverseExt
(* Ordinary procedures enter the extension engine only by explicit lift. *)
fun lifted_reducer data = Traverse.lift (OrdinaryTraverse.REDUCER data)
structure simpLib = simpExtLib
structure pureSimps =
struct
  val PURE_ss = simpExtLib.lift_ssfrag OrdinaryPure.PURE_ss
  val pure_ss = simpExtLib.lift_simpset OrdinaryPure.pure_ss
end
structure boolSimps =
struct
  open OrdinaryBool
  local val L = simpExtLib.lift_ssfrag in
  val bool_ss = simpExtLib.lift_simpset OrdinaryBool.bool_ss
  val BOOL_ss = L BOOL_ss  val CONG_ss = L CONG_ss  val ABBREV_ss = L ABBREV_ss
  val CONJ_ss = L CONJ_ss  val DISJ_ss = L DISJ_ss  val NOT_ss = L NOT_ss
  val COND_elim_ss = L COND_elim_ss  val LIFT_COND_ss = L LIFT_COND_ss
  val UNWIND_ss = L UNWIND_ss  val ETA_ss = L ETA_ss  val LET_ss = L LET_ss
  val literal_case_ss = L literal_case_ss  val DNF_ss = L DNF_ss
  val EQUIV_EXTRACT_ss = L EQUIV_EXTRACT_ss  val NORMEQ_ss = L NORMEQ_ss
  val LABEL_CONG_ss = L LABEL_CONG_ss  val HIDE_ss = L HIDE_ss
  end
end
structure congLib = congExtLib
structure T = TraverseExt

local open HolKernel boolLib testutils in

fun valid tac goal = #1 (runtac (VALID tac) goal)

fun has_double_neg tm =
  can (find_term (fn subtm =>
    is_neg subtm andalso is_neg (dest_neg subtm))) tm

fun goal_has_double_neg (asms, concl) =
  List.exists has_double_neg (concl :: asms)

end

end (* struct *)
