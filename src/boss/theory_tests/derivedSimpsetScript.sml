Theory derivedSimpset
Ancestors
  hol

open testutils

(* bossLib.boss_ss is derived from the stateful simpset, and simp, rw, fs
   and the rest resolve through it.  It has to move whenever the simpset
   moves: a derived value left behind keeps serving a simpset that
   predates rewrites the theory has since declared, and the reader never
   finds out.

   It used to be a suspension in a slot of its own, refreshed by a
   notification that the uninitialised path did not send.  A [simp]
   definition was then parked while boss_ss still predated it, and this
   shape of proof -- which mentions no simpset and no pattern match --
   failed for want of its own theory's rewrite. *)

Datatype: dsimp = DL | DE | DG
End

Definition k_def[simp]:
  (k DG = DL) /\ (k DL = DG) /\ (k DE = DE)
End

fun both nm inp expected =
    let val ctxt = Context.snapshot()
    in
      convtest (nm ^ " (srw_ss_of)",
                simpLib.SIMP_CONV (BasicProvers.srw_ss_of ctxt) [],
                inp, expected);
      convtest (nm ^ " (boss_ss_of)",
                simpLib.SIMP_CONV (bossLib.boss_ss_of ctxt) [],
                inp, expected)
    end

val _ = both "a [simp] definition reaches both" “k DL” “DG”

(* the same, on the augment_srw_ss path rather than the delta path *)
Definition j_def:
  j DG = DE
End

val _ = BasicProvers.augment_srw_ss [simpLib.rewrites [j_def]]

val _ = both "augment_srw_ss reaches both" “j DG” “DE”

(* and end to end: the literal proof shape that regressed *)
Theorem k_eq_DE[simp]:
  !x. (k x = DE) <=> (x = DE)
Proof
  Cases >> simp[]
QED

(* A deriver registered while the simpset is already initialised has to
   be put into the state that is current: init_state_of leaves such a
   state alone, so registering cannot rely on it.  Get that wrong and
   nothing breaks -- every read just derives afresh, forever, instead of
   sharing.  Counting derivations is what tells the two apart. *)
val derivations = ref 0
fun counting_deriver _ () = (derivations := !derivations + 1; ())

val _ = BasicProvers.srw_ss ()   (* so the state is certainly initialised *)

val {get_of = counted_of, ...} =
    BasicProvers.make_simpset_derived_value
      "derivedSimpset.counted" counting_deriver ()

val _ = let
  val before_reads = !derivations
  val _ = counted_of (Context.snapshot())
  val _ = counted_of (Context.snapshot())
  val n = !derivations - before_reads
in
  tprint "a deriver registered after initialisation is shared";
  (* the entry is a suspension, so two reads of one state force it once *)
  if n <= 1 then OK()
  else die ("derived " ^ Int.toString n ^ " times over two reads")
end

(* and it moves with the simpset like any other: a transition must
   produce a state whose entry derives afresh *)
val _ = let
  val _ = counted_of (Context.snapshot())
  val before_upd = !derivations
  val _ = BasicProvers.augment_srw_ss [simpLib.rewrites []]
  val _ = counted_of (Context.snapshot())
in
  tprint "a simpset transition re-derives it";
  if !derivations > before_upd then OK()
  else die "the value did not move with the simpset"
end
