open HolKernel Parse boolLib
open testutils TotalDefn
val _ = Feedback.emit_MESG := false
val _ = tprint "Testing mutually recursive function definition"

val f_def = Define`
  (f x = if x = 0 then T else ~g(x - 1)) /\
  (g x = if x = 0 then F else ~f(x - 1))
` handle _ => die "FAILED!"
val _ = print "OK\n";

val _ = tprint "Testing definition over literals"

val h_def = Define`
  (h 0 = T) /\ (h 1 = F)
`;

val _ = let
  val cs = strip_conj (concl h_def)
  val _ = length cs = 2 orelse die "FAILED!"
  val _ = List.all (is_const o rhs) cs orelse die "FAILED!"
in
  print "OK\n"
end
