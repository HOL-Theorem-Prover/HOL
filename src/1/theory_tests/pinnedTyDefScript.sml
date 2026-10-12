Theory pinnedTyDef[bare]
Libs
  HolKernel Parse boolLib testutils

(* A context pin used to answer a thread's reads from the pinned
   context while sending its writes to the live cell.
   Thm.prim_type_definition declared its new type operator and then
   looked that name up again to build the theorem, so under a pin it
   declared one type and described another -- the one the declaration
   had just replaced.  Two TYPE_DEFINITION theorems about the same type
   followed, one saying it has one element and the other two, and F
   with them.

   Both halves are closed now: prim_type_definition builds its theorem
   from the mint it is handed (Type.prim_mk_new_type), and a pinned
   write goes to the pin, so a declaration and any later lookup of it
   agree.  Either alone would do for this test; what it pins down is
   the property they both serve, that the theorem describes the type
   that was declared for it. *)

val two_elems =
    prove (“∃x:bool. (λx:bool. T) x”,
           EXISTS_TAC “T” THEN BETA_TAC THEN REWRITE_TAC [])

val one_elem =
    prove (“∃x:bool. (λx:bool. x) x”,
           EXISTS_TAC “T” THEN BETA_TAC THEN REWRITE_TAC [])

(* the representing type of |- ?rep : ty -> 'a. TYPE_DEFINITION P rep *)
fun repty th = #1 (Type.dom_rng (type_of (#1 (dest_exists (concl th)))))

val th1 = Theory.Definition.new_type_definition ("t", two_elems)

(* what the name "t" stands for with no pin anywhere in sight *)
val t_before =
    Type.mk_thy_type {Thy = current_theory(), Tyop = "t", Args = []}

val _ = tprint "unpinned type definition describes the type it declared"
val _ = if Type.compare (repty th1, t_before) = EQUAL then OK()
        else die "FAILED: th1 is not about the type it declared"

val ctx0 = Context.snapshot ()

val th2 = Context.with_context ctx0
            (fn () => Thm.prim_type_definition ("t", one_elem)) ()

val _ = tprint "pinned type definition describes the type it declared"
val _ = if Type.compare (repty th2, t_before) <> EQUAL then OK()
        else die "FAILED: th2 describes the type its declaration replaced"
