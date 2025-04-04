open HolKernel Parse boolLib bossLib;

open injected_strlit2Theory
open testutils

val _ = new_theory "injected_strlit3";

(* check that the string injections from the base theory really have been
   removed; the SINJ2 form will print to itself if this has been done *)
val _ = tpp "SINJ2 \"foo\""
val _ = tprint "Checking that ‹foo bar› parses to variable injection"
val _ = require_msg
            (check_result
             (fn t => is_var (rator t) handle HOL_ERR _ => false))
            term_to_string
            Parse.Term
            ‘‹foo bar›’
val _ = testutils.tpp "«bar foo»"


val _ = export_theory();
