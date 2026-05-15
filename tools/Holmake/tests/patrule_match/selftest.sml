open testutils Holmake_types

(* Phase-2 matcher tests.  Parse `sample' into a patrules list via
   ReadHMF, then call match_pattern_rules over a handful of synthetic
   targets and assert on the returned dependencies and post-
   substitution commands. *)

val (env, _, prs, _) = ReadHMF.read "sample" (base_environment())

(* Match-pure selftest: prereq existence is irrelevant here, so feed
   the matcher a trivially-satisfied predicate.  The dispatcher
   integration test (patrule_e2e) exercises the realistic predicate. *)
fun match t = match_pattern_rules (fn _ => true) env prs t

fun ri_str NONE = "NONE"
  | ri_str (SOME {dependencies, commands}) =
    "{deps=[" ^ String.concatWith "," dependencies ^
    "], cmds=[" ^ String.concatWith ";" commands ^ "]}"

fun check pred = check_result pred
fun req pred = require_msg (check pred) ri_str match

(* simple match: %.tex: %.smd *)
val _ = tprint "Simple pattern matches and substitutes stem into deps"
val _ = req (fn SOME {dependencies=["chapter1.smd"], commands=[c]} =>
                 c = "pandoc -o chapter1.tex chapter1.smd"
              | _ => false) "chapter1.tex"

(* automatic variables: %.uo %.ui: %.sml common.ui with recipe
   "mosmlc -c $* stem=$* deps=$^" *)
val _ = tprint "$* (stem) and $^ (all deps) expand in the recipe"
val _ = req (fn SOME {dependencies=["foo.sml", "common.ui"], commands=[c]} =>
                 c = "mosmlc -c foo stem=foo deps=foo.sml common.ui"
              | _ => false) "foo.uo"

(* multi-target rule: the same rule matches the second target form too *)
val _ = tprint "Multi-target rule matches via the second target form"
val _ = req (fn SOME {dependencies=["bar.sml", "common.ui"], commands=_} =>
                 true
              | _ => false) "bar.ui"

(* no match anywhere *)
val _ = tprint "Target with no matching pattern returns NONE"
val _ = req (fn NONE => true | _ => false) "no_such.exe"

(* first match wins: chapter1.tex is matched by the .tex rule, even
   though the third rule's `%-tag.out` pattern doesn't apply.  Make
   the test sharper: a target that *only* the third rule matches. *)
val _ = tprint "Third (later) rule still reached when earlier ones don't match"
val _ = req (fn SOME {dependencies=["data.in", "extra.dat"], commands=[c]} =>
                 c = "cp data.in data-tag.out"
              | _ => false) "data-tag.out"

(* stem includes a directory component *)
val _ = tprint "Stem can contain a directory separator"
val _ = req (fn SOME {dependencies=["sub/x.smd"], commands=[c]} =>
                 c = "pandoc -o sub/x.tex sub/x.smd"
              | _ => false) "sub/x.tex"
