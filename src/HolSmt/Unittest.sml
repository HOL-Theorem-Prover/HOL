(* Unit tests for HolSmtLib *)

structure Unittest :> Unittest =
struct

open HolKernel Parse boolLib bossLib

(*****************************************************************************)
(* helper functions                                                          *)
(*****************************************************************************)

fun die s =
  if !Globals.interactive then
    raise (Fail s)
  else (
    print ("\n" ^ s ^ "\n");
    OS.Process.exit OS.Process.failure
  )

fun assert (x, msg) = if x then () else die ("FAIL: " ^ msg)

(* Make sure two theorems are identical *)
fun compare_thms thm_pair =
let
  val hyps_pair = Lib.pair_map Thm.hypset thm_pair
  val (concl1, concl2) = Lib.pair_map Thm.concl thm_pair
  val () = assert (HOLset.equal hyps_pair,
    "theorem hypotheses are different")
  val () = assert (Term.term_eq concl1 concl2,
    "theorem conclusions are different")
in
  ()
end

(*****************************************************************************)
(* test definitions                                                          *)
(*****************************************************************************)

(* Test: `Z3_ProofReplay.remove_definitions` works without any definitions *)
fun remove_defs_no_defs () = ([], [])

(* Test: `Z3_ProofReplay.remove_definitions` works with a duplicate definition *)
fun remove_defs_dup () = ([
  ``(z1:num) = x + 1``,
  ``(z2:num) = z1 + 2``,
  ``(z2:num) = (x + 1) + 2``
], [``(z1:num)``, ``(z2:num)``])

(* Test: `Z3_ProofReplay.remove_definitions` works with the following set of
   (tricky) definitions, which can cause an exponential term blow-up in a
   naive implementation of `remove_definitions`:

   a1 = 1
   b1 = 1
   a2 = a1 + a1
   b2 = b1 + b1
   ...
   x = an
   x = bn

   Credit: Tjark Weber for coming up with this scenario. *)
fun remove_defs_tricky1 () =
let
  val asl = [
    ``(a1:num) = 1``,
    ``(b1:num) = 1``,
    ``(x:num) = a128``,
    ``(x:num) = b128``
  ]
  val varl = [``(a1:num)``, ``(b1:num)``, ``(a128:num)``, ``(b128:num)``,
    ``(x:num)``]

  (* `gen_def` creates a definition of the form ``si = s(i-1) + s(i-1)`` *)
  fun gen_def (i, s) =
  let
    val si = Term.mk_var (s ^ Int.toString i, numSyntax.num)
    val si_1 = Term.mk_var (s ^ Int.toString (i - 1), numSyntax.num)
  in
    (si, boolSyntax.mk_eq (si, numSyntax.mk_plus (si_1, si_1)))
  end

  (* Add ``ai = a(i-1) + a(i-1)`` and the same for ``bi``, for all 1 < i <= n *)
  fun add_defs (n, asl, varl) =
    if n = 1 then
      (asl, varl)
    else
      let
        val (an, an_def) = gen_def (n, "a")
        val (bn, bn_def) = gen_def (n, "b")
      in
        add_defs (n - 1, an_def :: bn_def :: asl, an :: bn :: varl)
      end
in
  add_defs (128, asl, varl)
end

(* Test: `Z3_ProofReplay.remove_definitions` works with the following set of
   (tricky) definitions, which can cause an exponential term blow-up in a
   naive implementation of `remove_definitions`:

   x = 1000
   y = 2000
   z1 = x + 1
   z2 = y + 1

   z3 =   z2    + (y + 1) +   z1
   z3 = (y + 1) +    z2   + (x + 1)

   z4 =          z3         + (z2 + z2 + z1) +   z1
   z4 = (z2 + z2 + (x + 1)) +       z3       + (x + 1)

   (...)

   z64 =          z63          + (z62 + z62 + z1) +   z1
   z64 = (z62 + z62 + (x + 1)) +        z63       + (x + 1)

   ... except we'll go all the way up to z128 instead of z64 *)
fun remove_defs_tricky2 () =
let
  val asl = [
    ``(x:num) = 1000``,
    ``(y:num) = 2000``,
    ``(z1:num) = x + 1``,
    ``(z2:num) = y + 1``,
    ``(z3:num) = z2 + (y + 1) + z1``,
    ``(z3:num) = (y + 1) + z2 + (x + 1)``
  ]
  val varl = List.map (fn t => Lib.fst (boolSyntax.dest_eq t)) asl

  fun add3 (a, b, c) = numSyntax.mk_plus (numSyntax.mk_plus (a, b), c)

  (* `gen_def1` creates a definition of the form:
       ``zi = z(i-1) + (z(i-2) + z(i-2) + z1) + z1`` *)
  fun gen_def1 i =
  let
    val z1 = Term.mk_var ("z1", numSyntax.num)
    val zi = Term.mk_var ("z" ^ Int.toString i, numSyntax.num)
    val zi_1 = Term.mk_var ("z" ^ Int.toString (i - 1), numSyntax.num)
    val zi_2 = Term.mk_var ("z" ^ Int.toString (i - 2), numSyntax.num)
    val middle_addend = add3 (zi_2, zi_2, z1)
    val sum = add3 (zi_1, middle_addend, z1)
  in
    (zi, boolSyntax.mk_eq (zi, sum))
  end

  (* `gen_def2` creates a definition of the form:
       ``zi = (z(i-2) + z(i-2) + (x + 1)) + z(i-1) + (x + 1) *)
  fun gen_def2 i =
  let
    val xp1 = ``(x:num) + 1``
    val zi = Term.mk_var ("z" ^ Int.toString i, numSyntax.num)
    val zi_1 = Term.mk_var ("z" ^ Int.toString (i - 1), numSyntax.num)
    val zi_2 = Term.mk_var ("z" ^ Int.toString (i - 2), numSyntax.num)
    val first_addend = add3 (zi_2, zi_2, xp1)
    val sum = add3 (first_addend, zi_1, xp1)
  in
    (zi, boolSyntax.mk_eq (zi, sum))
  end

  (* Add the definitions `gen_def1 i` and `gen_def2 i`, for all 3 < i <= n *)
  fun add_defs (n, asl, varl) =
    if n = 3 then
      (asl, varl)
    else
      let
        val (v1, def1) = gen_def1 n
        val (v2, def2) = gen_def2 n
      in
        add_defs (n - 1, def1 :: def2 :: asl, v1 :: v2 :: varl)
      end
in
  add_defs (128, asl, varl)
end

(* Test: `Z3_ProofReplay.remove_definitions` works with the following set of
   definitions which are not originally circular, but can become circular due
   to term unification. Credit: Tjark Weber *)
fun remove_defs_circular1 () = ([
    ``(a:num) = 1``,
    ``(b:num) = a``,
    ``(x:num) = a``,
    ``(x:num) = b``
], [``(a:num)``, ``(b:num)``, ``(x:num)``])

(* Test: `Z3_ProofReplay.remove_definitions` works with the following set of
   definitions which are not originally circular, but can become circular due
   to term unification. Credit: Tjark Weber *)
fun remove_defs_circular2 () = ([
    ``(a:num) = 1``,
    ``(b:num) = a``,
    ``(x:num) = b``,
    ``(x:num) = a``
], [``(a:num)``, ``(b:num)``, ``(x:num)``])

(* Wrapper for `Z3_ProofReplay.remove_definitions` unit tests *)
fun remove_defs_test get_definitions_fn =
let
  (* Create a simple theorem *)
  val thm = Thm.REFL ``i:num``
  (* Add a few hypotheses that should not be removed, and which coincidentally
     look like definitions *)
  val thm = Drule.ADD_ASSUM ``(i:num) = 7`` thm
  val thm = Drule.ADD_ASSUM ``(j:num) = i + 3`` thm
  (* Add definitions (which should be removed) *)
  val (asl, varl) = get_definitions_fn ()
  val vars = List.foldl (Lib.flip HOLset.add) Term.empty_tmset varl
  (* Let's orient definitions in the same way we do during proof replay *)
  val orient = boolSyntax.mk_eq o (Library.orient_def vars) o boolSyntax.dest_eq
  val asl = List.map orient asl
  val defs = List.foldl (Lib.flip HOLset.add) Term.empty_tmset asl
  val thm_with_defs = List.foldl (Lib.uncurry Drule.ADD_ASSUM) thm asl
  (* Remove definitions *)
  val final_thm = Z3_ProofReplay.remove_definitions (defs, vars, thm_with_defs)
in
  (* Make sure the resulting theorem is equal to the one before definitions
     were added *)
  compare_thms (thm, final_thm)
end

(*****************************************************************************)
(* actually perform tests                                                    *)
(*****************************************************************************)

fun run_test (name, f) =
let
  val () = print ("test " ^ name ^ "...")
  val () = Profile.reset_all ()
  val () = Profile.profile name f ()
  val results = Profile.results ()
  val result = Lib.assoc name results
  val elapsed = #real result
  val elapsed_str = Time.fmt 2 elapsed
  val () = print (" OK (elapsed: " ^ elapsed_str ^ "s)\n")
  val () = Profile.reset_all ()
in
  ()
end

fun run_unittests () =
let
  val () = print "Running unit tests...\n\n"
  val tests = [
    ("remove_definitions_no_defs", fn () => remove_defs_test remove_defs_no_defs),
    ("remove_definitions_dup", fn () => remove_defs_test remove_defs_dup),
    ("remove_definitions_tricky1", fn () => remove_defs_test remove_defs_tricky1),
    ("remove_definitions_tricky2", fn () => remove_defs_test remove_defs_tricky2),
    ("remove_definitions_circular1", fn () => remove_defs_test remove_defs_circular1),
    ("remove_definitions_circular2", fn () => remove_defs_test remove_defs_circular2)
  ]
  val () = List.app run_test tests
  val () = print "\ndone, all unit tests successful.\n"
in
  ()
end

end (* struct *)
