(* ========================================================================= *)
(* Version of the MESON procedure a la PTTP. Various search options.         *)
(* ========================================================================= *)


signature mesonLib =
sig
type thm = Thm.thm
type tactic = Abbrev.tactic;

   val depth     : bool ref
   val prefine   : bool ref
   val precheck  : bool ref
   val dcutin    : int ref
   val skew      : int ref
   val cache     : bool ref
   val chatting  : int ref
   val max_depth : int ref

   val GEN_MESON_TAC : int -> int -> int -> thm list -> tactic
   val MESON_TAC     : thm list -> tactic
   val ASM_MESON_TAC : thm list -> tactic

end (* sig *)
