(* tests for Hol_datatype *)

open HolKernel bossLib

val _ = Feedback.emit_MESG := false
val _ = Feedback.emit_ERR := false

fun Hol_datatype s q = let
  val _ = bossLib.Hol_datatype q
      handle HOL_ERR e => (TextIO.output(TextIO.stdErr,
                                         "Defining "^s^" failed with HOL_ERR "^
                                         Feedback.format_ERR e);
                           Process.exit Process.failure)
in
  ()
end

val _ = Hol_datatype "type1" `type1 = one_constructor`
val _ = Hol_datatype "type2" `type2 = ##`;
val _ = Hol_datatype "type3" `type3 = /\`;
val _ = Hol_datatype "type4" `type4 = /\ | \/ | (|) | feh`;
val _ = Hol_datatype "type4" `type5 = foo of num | bar of 'a`;

val _ = Process.exit Process.success;
