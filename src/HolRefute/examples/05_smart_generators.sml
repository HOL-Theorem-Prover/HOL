(* ===================================================================== *)
(*  HolRefute by example, 5: smart generators                            *)
(*                                                                       *)
(*  When a conjecture is guarded by an inductive predicate or a          *)
(*  Horn-shaped Boolean function, Refute does not generate values and    *)
(*  throw away those failing the guard: it mode-compiles the premise     *)
(*  into an enumerator that produces only values satisfying it.  That is *)
(*  the difference between finding a counterexample and testing          *)
(*  nothing.                                                             *)
(*                                                                       *)
(*      ../../bin/hol --holstate=refuteheap \                            *)
(*          < examples/05_smart_generators.sml                           *)
(* ===================================================================== *)

load "Refute";
open Refute;

(* Sections 1 to 5 pin the exhaustive backend, so that what you read is
   the smart plan's own answer and not some other backend's, and stop at
   the first potential counterexample rather than searching on for a
   certifiable one.  Sections 6 and 7 need neither restriction. *)

val smart = !the_config
  |> upd_backends (SOME ["exhaustive"])
  |> upd_abort_potential true;

(* --------------------------------------------------------------------- *)
(* 1.  An inductive premise                                              *)
(*                                                                       *)
(* Only every other natural satisfies [even_rel].  Refute compiles the   *)
(* Hol_reln clauses into a positive enumerator and walks the derivation  *)
(* tree, so it reaches the counterexample in a handful of tests.  Write  *)
(* the step with SUC: the mode compiler inverts constructor patterns,    *)
(* not arithmetic, and [even_rel (n + 2)] leaves it with no executable   *)
(* output mode.                                                          *)
(* --------------------------------------------------------------------- *)

val (even_rel_rules, even_rel_ind, even_rel_cases) = Hol_reln `
  (even_rel 0) /\
  (!n. even_rel n ==> even_rel (SUC (SUC n)))`;

refute smart ``even_rel n ==> n < 5``;

(* ==> Counterexample n = 6, backend exhaustive, substrate native,
       after 4 tests.  Its certainty is Potential ["evaluation stuck
       on: even_rel"]: a Hol_reln constant carries no computeLib
       equations, so certification cannot evaluate the premise back.
       Proving a computational equation for [even_rel] and adding it to
       the compset is what promotes such a hit to Genuine; see 02 for
       the certainty levels. *)

(* --------------------------------------------------------------------- *)
(* 2.  Fuel, not a schedule                                              *)
(*                                                                       *)
(* [upd_depth] is the per-plan fuel given to a smart enumeration         *)
(* (default 10).  Because every smart enumeration is fuel-bounded,       *)
(* exhausting it is always reported as incomplete: "search space not     *)
(* exhausted" never means "theorem".  Starve the fuel and the same goal  *)
(* goes quiet.                                                           *)
(* --------------------------------------------------------------------- *)

refute (upd_depth 2 smart) ``even_rel n ==> n < 5``;

(* ==> Unknown ["exhaustive: search space not exhausted"].  The
       enumeration runs out of fuel before it derives even_rel 6. *)

refute (upd_depth 20 smart) ``even_rel n ==> n < 5``;

(* ==> Counterexample n = 6 again, still after 4 tests: the extra fuel
       is a bound, not a schedule, so it costs nothing here. *)

(* --------------------------------------------------------------------- *)
(* 3.  With smart generators switched off                                *)
(*                                                                       *)
(* [upd_smart_generators false] restores plain generate-and-guard        *)
(* planning.  Such a plan has to evaluate the premise on each candidate, *)
(* and a Hol_reln constant is not executable, so the exhaustive backend  *)
(* is now excluded outright by the executability gate.  Discharging that *)
(* gate is exactly what the smart plan did in section 1.                 *)
(* --------------------------------------------------------------------- *)

refute (upd_smart_generators false smart)
  ``even_rel n ==> n < 5``;

(* ==> Unknown ["not executable: even_rel"] *)

(* --------------------------------------------------------------------- *)
(* 4.  A relation defined over another definition                        *)
(*                                                                       *)
(* [path] is reachability along [edge].  The interesting counterexample  *)
(* is a reachable node the conjecture forgot about, and mode analysis    *)
(* has to chain the two premises to reach it.  [edge]'s step is written  *)
(* with SUC for the same reason as section 1: [y = x + 1] gives mode     *)
(* analysis nothing to invert, and the goal falls back to "not           *)
(* executable: path".                                                    *)
(* --------------------------------------------------------------------- *)

val edge_def = Define `edge x y <=> (y = SUC x) /\ y <= 3`;

val (path_rules, path_ind, path_cases) = Hol_reln `
  (!x. path x x) /\
  (!x y z. edge x y /\ path y z ==> path x z)`;

(* True: reachability only ever moves upwards.                           *)
refute smart ``path x y ==> x <= y``;

(* ==> Unknown ["exhaustive: search space not exhausted"].  Nothing was
       refuted, and, fuel being what it is, that is as far as the
       report goes. *)

(* False: 3 is reachable from 0.                                         *)
refute smart ``path 0 y ==> y <= 2``;

(* ==> Counterexample y = 3, backend exhaustive, substrate native.
       Potential ["evaluation stuck on: path"], for the same reason as
       in section 1. *)

(* --------------------------------------------------------------------- *)
(* 5.  Premise order                                                     *)
(*                                                                       *)
(* Mode analysis reorders premises so that enumerable ones run before    *)
(* the tests that consume their outputs.  [upd_reorder_premises false]   *)
(* keeps the order you wrote, which is occasionally what you want when   *)
(* investigating why a plan behaves as it does.                          *)
(* --------------------------------------------------------------------- *)

refute (upd_reorder_premises false smart)
  ``path 0 y ==> y <= 2``;

(* ==> the same Counterexample y = 3.  On this goal the order written in
       the clause already is the order mode analysis would choose, so
       the flag makes no observable difference. *)

(* --------------------------------------------------------------------- *)
(* 6.  Boolean functions with exhaustive Horn-shaped equations           *)
(*                                                                       *)
(* A Hol_reln premise is not the only thing that gets mode-compiled: a   *)
(* Boolean function whose defining equations are Horn-shaped works too.  *)
(* Here Refute enumerates sorted lists rather than filtering arbitrary   *)
(* ones, so the four-element witness shows up quickly.  [Define] also    *)
(* puts the equations in the compset, so this counterexample certifies.  *)
(* --------------------------------------------------------------------- *)

val sortedp_def = Define `
  (sortedp [] = T) /\
  (sortedp [x : num] = T) /\
  (sortedp (x :: y :: t) = (x <= y /\ sortedp (y :: t)))`;

refute_def ``sortedp xs ==> LENGTH xs <= 3``;

(* ==> Counterexample xs = [0; 0; 0; 0] after 11 tests, backend
       exhaustive, substrate native.  Genuine, with the certifying
       theorem |- ~!xs. sortedp xs ==> LENGTH xs <= 3. *)

(* --------------------------------------------------------------------- *)
(* 7.  The same plan on every substrate                                  *)
(*                                                                       *)
(* Compute and Cv define the same structurally recursive HOL list        *)
(* enumerators, and native SML preserves the same clause and premise     *)
(* order, so a smart plan behaves the same way whichever substrate runs  *)
(* it.  Only the speed differs.                                          *)
(* --------------------------------------------------------------------- *)

fun smart_on substrate =
  refute
    (!the_config
       |> upd_substrate substrate
       |> upd_backends (SOME ["exhaustive"])
       |> upd_quiet true)
    ``sortedp xs ==> LENGTH xs <= 3``;

map (fn substrate =>
  case smart_on substrate of
      Counterexample (cex :: _) =>
        (#substrate cex, map (Parse.term_to_string o #2) (#bindings cex))
    | _ => ("none", []))
  [NativeSML, Cv, Compute];

(* ==> [("native", ["[0; 0; 0; 0]"]), ("cv", ["[0; 0; 0; 0]"]),
        ("compute", ["[0; 0; 0; 0]"])] *)
