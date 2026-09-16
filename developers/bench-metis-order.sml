(* ----------------------------------------------------------------------
   How much does a metis call depend on what the process proved before?

   metis weights clauses by how often they hold in a finite model of the
   axioms (mlibSupport.clause_weight).  The valuations behind "how
   often" are sampled, and the sampling used to draw from one generator
   per process, seeded when mlibModel loaded and never reset, so every
   call started wherever the previous one stopped.  On a hard search
   that decided the whole cost: repeats of one relevant-logic theorem
   ranged from 0.5s to 40s in a single session, and the theory built in
   either 5.6s or 32s depending on nothing but how far the generator had
   got.  The models are now seeded from the problem instead.

   This is a measurement, not a regression test, and the distinction is
   worth stating because it cost an afternoon to learn: the goals below
   are cheap enough to run unattended, and at that size the model
   barely steers, so they report the same small spread whether or not
   the generator is shared.  A harness that passes either way is worth
   nothing.  The case that does discriminate needs a search where the
   model dominates, and the one to hand is a whole example theory:

       bin/Holmake -C examples/logic/relevant-logic cleanDeps
       rm -f examples/logic/relevant-logic/SlaneyRLTheory.* \
             examples/logic/relevant-logic/.hol/objs/SlaneyRLTheory.*
       bin/Holmake -C examples/logic/relevant-logic SlaneyRLTheory.uo

   and, to see the swing directly, prefix that script with k calls to
   mlibModel.check to advance the old generator: over k = 0..8 the build
   took anywhere from 5s to 62s.

   What the columns below do show is the residual, which lives upstream
   of metis: HOL's CNF names its skolem constants from a genvar counter
   and mlibThm.FRESH_VARS renames variables from another, so the symbol
   names reaching metis differ per call, and model interpretations are
   md5-derived from those names (mlibModel.randomize).  Repeats of one
   goal therefore still search a little differently.  Primitive
   inferences rather than the clock, because a search that went
   differently translates a different proof and the count says so
   without the timing noise.  `set_trace "metis" 2` adds the seed each
   call used: those should not move.

   The workload is first-order logic over uninterpreted symbols (`i` for
   implication, `P` for provability -- a relevance logic).  metisTools'
   hol_fix interprets none of it, so the model is guiding on noise.

   Run:
       bin/hol run developers/bench-metis-order.sml

   ---------------------------------------------------------------------- *)

open HolKernel boolLib bossLib;

(* TAC_PROOF wants a current theory; nothing is exported from it *)
val () = new_theory "bench_metis_order"

val REPEATS = 6

val axioms = “
  (!a. P (i a a)) /\
  (!a b c. P (i (i a (i b c)) (i b (i a c)))) /\
  (!a b c. P (i (i a b) (i (i b c) (i a c)))) /\
  (!a b. P (i a (i a b)) ==> P (i a b)) /\
  (!a b. P a /\ P (i a b) ==> P b)
”

val goals =
  [("assertion", “!a b. P (i a (i (i a b) b))”),
   ("prefixing", “!a b c. P (i (i a b) (i (i c a) (i c b)))”),
   ("suffixing", “!a b c. P (i (i a b) (i (i b c) (i a c)))”),
   ("contract3", “!a b c. P (i (i a (i a (i a b))) (i a b))”)]

val secs = Real.fmt (StringCvt.FIX (SOME 2))

fun run_once tm =
  let
    val m = Count.mk_meter ()
    val t = Timer.startRealTimer ()
    val _ = prove(mk_imp(axioms, tm), strip_tac >> metis_tac[])
  in
    (#prims (Count.read m), Time.toReal (Timer.checkRealTimer t))
  end

(* left to right, spelt out: List.tabulate's order is unspecified, and
   whether the order of these calls matters is the question *)
fun repeat 0 _ = []
  | repeat k f = let val x = f () in x :: repeat (k - 1) f end

fun row lbl tag cells =
  StringCvt.padRight #" " 11 lbl ^ tag ^
  String.concat (map (StringCvt.padLeft #" " 8) cells)

fun report (nm, tm) =
  let
    val (ps,ts) = ListPair.unzip (repeat REPEATS (fn () => run_once tm))
    val lo = foldl Int.min (hd ps) ps
    val hi = foldl Int.max (hd ps) ps
    val spread = Real.fromInt hi / Real.fromInt (Int.max (lo,1))
  in
    print (row nm "prims" (map Int.toString ps) ^
           "   spread x" ^ secs spread ^ "\n");
    print (row "" "secs " (map secs ts) ^ "\n")
  end

val () = print ("\nsame goal, " ^ Int.toString REPEATS ^
                " times in one process\n\n")
val () = List.app report goals
