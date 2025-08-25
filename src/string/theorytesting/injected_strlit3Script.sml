Theory injected_strlit3
Ancestors
  injected_strlit2
Libs
  testutils

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


