open HolKernel Parse boolLib bossLib;

open modelCheckLib testutils;

(* To run this test, the environment variable HOL4_SMV_EXECUTABLE must be set to
   the full path of "NuSMV" [1] executation.

   [1] http://nusmv.fbk.eu
 *)

val ltl1 = ``LTL_SUNTIL (LTL_PROP (P_PROP a), LTL_PROP (P_PROP b))``;

val ltl2 = ``LTL_EVENTUAL (LTL_AND (LTL_PROP (P_PROP b),
                                    LTL_PNEXT (LTL_PALWAYS (LTL_PROP (P_PROP a)))))``;

val result1 = “LTL_EQUIVALENT_INITIAL
       (LTL_SUNTIL (LTL_PROP (P_PROP a),LTL_PROP (P_PROP b)))
       (LTL_EVENTUAL
          (LTL_AND
             (LTL_PROP (P_PROP b),
              LTL_PNEXT (LTL_PALWAYS (LTL_PROP (P_PROP a))))))”;

fun modelCheck_test1 () = let
    val test1 = model_check___ltl_equivalent_initial ltl1 ltl2;
in
  if aconv (concl (valOf test1)) result1 then OK ()
  else die ("Got " ^ term_to_string (concl (valOf test1)));
  Process.system ("rm " ^ (!model_check_temp_file))
end;

fun modelCheck_test2 () = let
  val test2 = model_check___ltl_equivalent ltl1 ltl2;
in
  if (isSome test2) then
    die ("Got " ^ term_to_string (concl (valOf test2)))
  else OK ();
  Process.system ("rm " ^ (!model_check_temp_file))
end;

val _ = modelCheck_test1 ();
val _ = modelCheck_test2 ();

val _ = Process.exit Process.success;
