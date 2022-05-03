open HolKernel Parse bossLib boolLib;

open simpLib realSimps Diff transcTheory isqrtLib;

open testutils;

fun diff_test (r as (n,f,df)) =
    let
      fun check res = aconv df (concl res);
    in
      tprint (n ^ ": " ^ term_to_string df);
      require_msg (check_result check) (term_to_string o concl) DIFF_CONV f
    end;

val _ = List.app diff_test [
      ("DIFFCONV00", “\x. exp x”,   “!x. ((\x. exp x) diffl (exp x * 1)) x”),
      ("DIFFCONV01", “\x. sin x”,   “!x. ((\x. sin x) diffl (cos x * 1)) x”),
      ("DIFFCONV02", “\x. cos x”,   “!x. ((\x. cos x) diffl (-sin x * 1)) x”),
      ("DIFFCONV03", “\x. tan x”,
                     “!x. cos x <> 0 ==> ((\x. tan x) diffl (inv (cos x pow 2) * 1)) x”),
      ("DIFFCONV04", “\x. ln x”,
                     “!x. 0 < x ==> ((\x. ln x) diffl (inv x * 1)) x”),
      ("DIFFCONV05", “\x. asn x”,   “!x. -1 < x /\ x < 1 ==>
                                         ((\x. asn x) diffl (inv (sqrt (1 - x pow 2)) * 1)) x”),
      ("DIFFCONV06", “\x. acs x”,   “!x. -1 < x /\ x < 1 ==>
                                         ((\x. acs x) diffl (-inv (sqrt (1 - x pow 2)) * 1)) x”),
      ("DIFFCONV07", “\x. atn x”,   “!x. ((\x. atn x) diffl (inv (1 + x pow 2) * 1)) x”),
      ("DIFFCONV08", “\x. x pow 3”, “!x. ((\x. x pow 3) diffl (3 * x pow (3 - 1) * 1)) x”),
      ("DIFFCONV09", “\x. (sin x) pow 2”,
                     “!x. ((\x. sin x pow 2) diffl (2 * sin x pow (2 - 1) * (cos x * 1))) x”),
      ("DIFFCONV10", “\x. sin (x pow 2)”,
                     “!x. ((\x. sin (x pow 2)) diffl
                           (cos (x pow 2) * (2 * x pow (2 - 1) * 1))) x”),
      ("DIFFCONV11", “\x. ln (x pow 2)”,
                     “!x. 0 < x pow 2 ==>
                          ((\x. ln (x pow 2)) diffl
                           (inv (x pow 2) * (2 * x pow (2 - 1) * 1))) x”)
    ];

val _ = Process.exit Process.success;
