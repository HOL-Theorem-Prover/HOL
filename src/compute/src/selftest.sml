open testutils HolKernel Parse boolLib computeLib

val _ = tprint "Checking monitoring output goes to Feedback MESG"

fun capture_mesg f x =
    let
      val captured = ref ([] : string list)
      fun out s = (captured := s :: !captured)
      val result = Lib.with_flag (Feedback.MESG_outstream, out) f x
    in
      (result, String.concat (List.rev (!captured)))
    end

fun monitor_and f x =
    Lib.with_flag
      (computeLib.monitoring, SOME (same_const boolSyntax.conjunction))
      f x

val _ = new_constant("result1", “:ind”)

val f1_def = new_definition(
  "f1",
  “f1 (x :ind) = result1”)

val P1_def = new_definition(
  "P1",
  “P1 (x :ind) = F”)

val P2_def = new_definition(
  "P2",
  “P2 (x :ind) = T”)

val _ = new_constant("result2", “:ind”)
val _ = new_constant("result3", “:ind”)

val f2_def = new_specification(
  "f2_def",
  ["f2"],
  prove(
    “∃f2. ∀x :ind. (P1 x ⇒ f2 x = result2) ∧ (P2 x ⇒ f2 x = result3)”,
    EXISTS_TAC “λx :ind. result3” >>
    REWRITE_TAC [P1_def, P2_def]))

val _ = computeLib.add_funs([f1_def, P1_def, P2_def, f2_def])

fun EVAL t = computeLib.CBV_CONV (!computeLib.the_compset) t

(* Check that `EVAL` reduces `t` to `t'` *)
fun assert_reduces_to t t' =
  let
    val red_thm = EVAL t
    val concl_t = concl red_thm
  in
    if not (is_eq concl_t) then
      die ("EVAL " ^
           Parse.term_to_string t ^
           " --> " ^
           Parse.term_to_string concl_t ^
           " (not an equality)\n")
    else
      let
        val (lhs_t, rhs_t) = dest_eq concl_t
      in
        if not (lhs_t ~~ t) then
          die ("EVAL " ^
               Parse.term_to_string t ^
               " returned bad theorem (LHS different from argument)\n")
        else if not (rhs_t ~~ t') then
          die ("EVAL " ^
               Parse.term_to_string t ^
               " --> " ^
               Parse.term_to_string rhs_t ^
               " (expected " ^
               Parse.term_to_string t' ^
               ")\n")
        else
          OK ()
      end
  end

val t1 = “x ∧ T”
val (th, s) = Feedback.trace ("Unicode", 0) (capture_mesg (monitor_and EVAL)) t1

val _ = if lhs (concl th) ~~ t1 andalso rhs (concl th) ~~ lhand (lhs (concl th))
        then
          if s = "x /\\ T <=> x\n" then OK()
          else die ("Bad message: " ^ s)
        else die ("Bad theorem: " ^ thm_to_string th)

val _ = assert_reduces_to “f1 y” “result1”;
val _ = assert_reduces_to “f2 z” “result3”;

(* Tests for seal and copy functions *)

val _ = tprint "Checking seal prevents adding rules for existing constants"
val sealed_cs = computeLib.seal (computeLib.new_compset [boolTheory.AND_CLAUSES])
val _ = let
  (* Trying to add more rules for /\ should fail on sealed compset *)
  val failed = (computeLib.add_thms [boolTheory.AND_CLAUSES] sealed_cs; false)
               handle HOL_ERR _ => true
in
  if failed then OK()
  else die "Expected exception when adding to sealed compset with existing const"
end

val _ = tprint "Checking seal allows adding rules for new constants"
val sealed_cs2 = computeLib.seal (computeLib.new_compset [])
val _ = let
  (* Adding rules for a new constant should succeed on sealed compset *)
  val _ = computeLib.add_thms [boolTheory.AND_CLAUSES] sealed_cs2
in
  OK()
end
handle HOL_ERR e => die ("Unexpected exception: " ^ message_of e)

val _ = tprint "Checking copy creates modifiable compset"
val copied_cs = computeLib.copy sealed_cs
val _ = let
  (* Adding more rules for existing /\ should succeed after copy *)
  val _ = computeLib.add_thms [boolTheory.AND_CLAUSES] copied_cs
in
  OK()
end
handle HOL_ERR e => die ("Unexpected exception after copy: " ^ message_of e)

val _ = tprint "Checking copy preserves evaluation behavior"
val test_cs = computeLib.new_compset [boolTheory.AND_CLAUSES]
val copied_test_cs = computeLib.copy test_cs
val _ = let
  val t = “T /\ T”
  val th1 = computeLib.CBV_CONV test_cs t
  val th2 = computeLib.CBV_CONV copied_test_cs t
in
  if rhs (concl th1) ~~ rhs (concl th2) then OK()
  else die "copy changed evaluation behavior"
end

val _ = tprint "Checking bool_compset is sealed"
val _ = let
  val failed = (computeLib.add_thms [boolTheory.COND_CLAUSES] computeLib.bool_compset; false)
               handle HOL_ERR _ => true
in
  if failed then OK()
  else die "bool_compset should be sealed"
end

(* More detailed sealing tests *)

val _ = tprint "Checking theorems with existing RHS constants work on sealed compsets"
(* This tests that from_term can look up existing constants without failing *)
val _ = let
  val base_cs = computeLib.seal (computeLib.new_compset [boolTheory.AND_CLAUSES])
  (* Define a theorem whose RHS mentions T (which is in base_cs via AND_CLAUSES) *)
  val new_thm = prove(“foo_const = T”, REWRITE_TAC [])
      handle HOL_ERR _ => TRUTH (* fallback if foo_const doesn't exist *)
  val _ = new_constant("test_const", “:bool”)
  val test_def = new_definition("test_def", “test_const = T”)
  (* Adding this should work even though T is on the RHS and in the sealed compset *)
  val _ = computeLib.add_thms [test_def] base_cs
in
  OK()
end
handle HOL_ERR e => die ("RHS lookup failed on sealed compset: " ^ message_of e)

val _ = tprint "Checking set_skip fails for existing constants in sealed compset"
val _ = let
  val cs = computeLib.seal (computeLib.new_compset [boolTheory.COND_CLAUSES])
  val failed = (computeLib.set_skip cs boolSyntax.conditional NONE; false)
               handle HOL_ERR _ => true
in
  if failed then OK()
  else die "set_skip should fail for existing constant in sealed compset"
end

val _ = tprint "Checking set_skip works for new constants in sealed compset"
val _ = let
  val cs = computeLib.seal (computeLib.new_compset [])
  (* This should succeed since COND is not in the empty compset *)
  val _ = computeLib.set_skip cs boolSyntax.conditional NONE
in
  OK()
end
handle HOL_ERR e => die ("set_skip failed for new constant: " ^ message_of e)

val _ = tprint "Checking set_skip works after copy"
val _ = let
  val cs = computeLib.seal (computeLib.new_compset [boolTheory.COND_CLAUSES])
  val cs' = computeLib.copy cs
  val _ = computeLib.set_skip cs' boolSyntax.conditional NONE
in
  OK()
end
handle HOL_ERR e => die ("set_skip after copy failed: " ^ message_of e)
