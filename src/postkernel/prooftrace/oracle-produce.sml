open HolKernel;
val () = Theory.new_theory "oracle_hyps";

val p = Term.mk_var ("p", Type.bool);
val q = Term.mk_var ("q", Type.bool);
val r = Term.mk_var ("r", Type.bool);
fun oracle sequent = Thm.mk_oracle_thm "PFT_ORACLE_REGRESSION" sequent;
fun save name th = ignore (Theory.save_thm (name, th));

val () = save "empty" (oracle ([], p));
val () = save "one" (oracle ([q], p));
val () = save "two" (oracle ([q, r], p));
val () = save "overlap" (oracle ([p, q], p));
val () = save "duplicate" (oracle ([q, q, r], p));
val () = Theory.export_theory ();

val () = Theory.new_theory "deduct_antisym";
val () = save "deduct" (Thm.deductAntisym
  (oracle ([q, r], p)) (oracle ([p], q)));
val () = save "deduct_reverse" (Thm.deductAntisym
  (oracle ([p, r], q)) (oracle ([q], p)));
val () = save "deduct_empty" (Thm.deductAntisym
  (Thm.ASSUME p) (Thm.ASSUME p));

val () = Theory.export_theory ();
val () = print "PFT_ORACLE_FIXTURES_PRODUCED\n";
