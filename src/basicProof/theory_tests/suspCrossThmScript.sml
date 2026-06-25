Theory suspCrossThm[bare]

(* A theorem -- whether a regular `Theorem`, a `Resume` body, or any
   other saved form -- may only consume already-finalised theorems.
   The only legal way to consume a still-suspended theorem X is to
   write `Resume X[label]` for one of its unsolved subgoals (#1963).

   Two rejection points exercised below: markerLib.resume catches the
   cross-theorem citation inside a Resume body, and
   boolLib.save_thm_attrs catches the same in a regular Theorem. *)

Libs HolKernel Parse boolLib markerLib testutils

Theorem th1:
  p ==> T
Proof
  suspend "l1"
QED

Theorem th2:
  q ==> T
Proof
  suspend "l2"
QED

val _ = shouldfail {
  testfn = (fn () =>
              resume {suspension_name = "th1", label_name = "l1"}
                     (MATCH_ACCEPT_TAC th2)),
  printarg = (fn _ =>
              "resume th1[l1] with MATCH_ACCEPT_TAC th2 (th2 suspended)"),
  printresult = (fn _ => "<unexpected success>"),
  checkexn =
    check_HOL_ERRexn (fn (_, fnm, msg) =>
        fnm = "resume" andalso
        String.isSubstring "still-suspended" msg)
} ()

(* A regular `Theorem foo Proof <body cites th2> QED` would inherit
   th2's suspendlabel hypothesis.  Going via save_thm_attrs directly
   exercises the same path the Theorem parser would. *)
val _ = shouldfail {
  testfn = (fn () =>
              boolLib.save_thm_attrs
                (DB_dtype.mkloc(#(FILE),#(LINE),true))
                (ThmAttribute.extract_attributes "foo", th2)),
  printarg = (fn _ =>
              "save_thm_attrs \"foo\" of a thm inheriting th2's slab"),
  printresult = (fn _ => "<unexpected success>"),
  checkexn =
    check_HOL_ERRexn (fn (_, fnm, msg) =>
        fnm = "save_thm_attrs" andalso
        String.isSubstring "still-suspended" msg)
} ()

(* Tidy up so the theory exits with no slab-bearing theorems left in
   the DB; this keeps the export_theory safety net happy. *)
Resume th1[l1]:
  strip_tac >> ACCEPT_TAC TRUTH
QED

Resume th2[l2]:
  strip_tac >> ACCEPT_TAC TRUTH
QED

Finalise th1
Finalise th2
