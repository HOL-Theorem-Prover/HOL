open testutils HolKernel Parse boolLib computeLib

val _ = tprint "Checking monitoring output goes to Feedback MESG"

fun capture_mesg f x =
    let
      val captured = ref ([] : string list)
      fun out s = (captured := s :: !captured)
      val result = Lib.with_flag (Feedback.MESG_outstream, out) f x
    in
      (result, String.concat (List.rev (!captured)))
    end

fun monitor_and f x =
    Lib.with_flag
      (computeLib.monitoring, SOME (same_const boolSyntax.conjunction))
      f x

val t = “x /\ T”
fun EVAL t = computeLib.CBV_CONV computeLib.the_compset t
val (th, s) = Feedback.trace ("Unicode", 0) (capture_mesg (monitor_and EVAL)) t

val _ = if lhs (concl th) ~~ t andalso rhs (concl th) ~~ lhand (lhs (concl th))
        then
          if s = "x /\\ T <=> x\n" then OK()
          else die ("Bad message: " ^ s)
        else die ("Bad theorem: " ^ thm_to_string th)
