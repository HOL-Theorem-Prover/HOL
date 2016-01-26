open HolKernel Parse boolLib

open monofldATheory

val _ = new_theory "monofldB";

val (write, read) = let
  val buf = ref ([] : string list)
  fun w s = (buf := s :: !buf)
  fun r () = let
    val result = String.concat (List.rev (!buf))
  in
    buf := [result];
    result
  end
in
  (w, r)
end

val _ = Feedback.MESG_outstream := write
val _ = Globals.interactive := true

val t = ``(r : 'a rcd) with myset := (\x. F)``;

val _ = assert (equal ``:'a rcd``) (type_of t)

val msg = read()
val _ = if msg = "" then print "No message\n"
        else raise Fail ("Message was: "^msg)

val _ = save_thm("MFB", TRUTH)

val _ = export_theory();
