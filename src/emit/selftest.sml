open HolKernel bossLib testutils
local open basis_emitTheory in end

val (is_con, thy, name, ty) = ConstMapML.apply ``bool$IN``
val _ = tprint "Testing ConstMapML information for bool$IN"

val _ = if thy <> "set" then die "FAILED!" else print "OK\n"

fun gh157() = let
  val gh157a_def = Define`gh157a = T`
  val gh157b_def = Define`gh157b = ~gh157a`;
  val _ = tprint "Emit should fail on missing def'n"
  fun exists p = OS.FileSys.access(Path.concat("ML", p),[])
in
  (with_flag (Feedback.emit_WARNING, false) (EmitML.eSML "bug") [EmitML.DEFN gh157b_def];
   die "FAILED!")
  handle HOL_ERR _ =>
         if List.exists exists ["bugML.sml", "bugML.sig"] then die "FAILED!\n"
         else print "OK\n"
end

val _ = trace ("Define.storage_message", 0) gh157 ()
