open HolKernel bossLib

val _ = Feedback.set_trace "Theory.save_thm_reporting" 0;

(* Ramana Kumar's beta-redex definition bug 14/09/2010 *)
val _ = tDefine "foo"
`foo x = if (\x. x) x then foo F else ()`
(WF_REL_TAC `measure (\x. if x then 1 else 0)`);

val _ = Process.exit Process.success;
