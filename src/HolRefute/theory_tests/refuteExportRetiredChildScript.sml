Theory refuteExportRetiredChild
Ancestors
  refuteExportRetired
Libs
  Refute

fun rejected_with fragment f =
  (f (); false) handle HOL_ERR e =>
    String.isSubstring fragment (Feedback.message_of e);
val neighbour_survived = rejected_with "incompatible" (fn () =>
  Refute.register_typedef
    {ty = ``:api_small``, abs = ``api_small_abs``, rep = ``api_small_rep``,
     absrep_thms = [refutePersistentTypeTheory.api_small_bij]});
val _ = if neighbour_survived then ()
        else raise Fail "retirement lost a neighbouring description";
val retired_absent = rejected_with "no exportable description" (fn () =>
  Refute.export_registrations [``:api_missing``]);
val _ = if retired_absent then ()
        else raise Fail "a retired description survived theory export";
