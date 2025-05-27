(* ========================================================================= *)
(* Create "relTheory" containing the relational semantics of a small         *)
(* imperative probabilistic language.                                        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories                                           *)
(* (Comment out "load" and "quietdec"s for compilation)                      *)
(* ------------------------------------------------------------------------- *)
(*
app load
  ["bossLib","realLib","rich_listTheory","stringTheory",
   "metisLib","posrealLib","expectationTheory","intLib"];
quietdec := true;
*)

open HolKernel Parse boolLib bossLib intLib realLib metisLib;
open combinTheory listTheory rich_listTheory stringTheory integerTheory
     realTheory posetTheory;
open posrealTheory posrealLib measureTheory;
open expectationTheory syntaxTheory;

(*
quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "rel"                                           *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "rel";

(* ------------------------------------------------------------------------- *)
(* Helpful proof tools                                                       *)
(* ------------------------------------------------------------------------- *)

val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val REVERSE = Tactical.REVERSE;
val lemma = I prove;

(* ------------------------------------------------------------------------- *)
(* Measures.                                                                 *)
(* ------------------------------------------------------------------------- *)

val point_measure_def = Define
  `point_measure (p : 'a -> bool) x =
   <| carrier := p;
      sets := UNIV;
      mu := \s. if x IN s then 1 else 0 |>`;

val linear_measure_def = Define
  `linear_measure p m1 m2 =
   <| carrier := m1.carrier;
      sets := m1.sets INTER m2.sets;
      mu := \s. p * m1.mu s + (1 - p) * m2.mu s |>`;

val ConvexClosed_def = Define
  `ConvexClosed =
   { s |
     !p. !m1 m2 :: s.
       p <= 1 /\ (m1.carrier = m2.carrier) ==>
       linear_measure p m1 m2 IN s }`;

(* ------------------------------------------------------------------------- *)
(* The HOL type we use to model relations.                                   *)
(* ------------------------------------------------------------------------- *)

val () = type_abbrev ("rel", Type `:'a state -> 'a state measure -> bool`);

(* ------------------------------------------------------------------------- *)
(* Well-formed relations.                                                    *)
(* ------------------------------------------------------------------------- *)

val Measure_def = Define
  `Measure =
   { m : 'a state measure |
     m IN ProbabilitySpace /\
     (m.carrier = UNIV) /\
     (m.sets = UNIV) /\
     countable m.carrier }`;

val Rel_def = Define
  `Rel =
   { r : 'a rel |
     (!s m. r s m ==> m IN Measure) /\
     (!s. { m | r s m } IN ConvexClosed) }`;

(* ------------------------------------------------------------------------- *)
(* Relation operations.                                                      *)
(* ------------------------------------------------------------------------- *)

val union_rel_def = Define
  `union_rel r1 r2 s m =
   ?p m1 m2.
     p <= 1 /\ r1 s m1 /\ r2 s m2 /\
     (m = linear_measure p m1 m2)`;

val lin_rel_def = Define
  `lin_rel p r1 r2 s m =
   ?m1 m2.
     r1 s m1 /\ r2 s m2 /\
     (m = linear_measure (p s) m1 m2)`;

(* Got stuck on sequential composition

val seq_rel_def = Define
  `seq_rel r1 r2 s m =
   ?m' m''.
     r1 s m' /\ (!s'. r2 s' (m'' s')) /\
     (m IN ProbabilitySpace) /\
     (m.carrier = UNIV) /\
     (m.sets = BIGINTER (IMAGE (\s'. (m'' s').sets)) UNIV) /\
     (m.mu = \a''. integrate m' UNIV (\s'. (m'' s').mu a''))`;
*)

(* ------------------------------------------------------------------------- *)
(* Relational semantics.                                                     *)
(* ------------------------------------------------------------------------- *)

(*
val rel_def = Define
  `(rel Abort = \s m. m IN Measure) /\
   (rel (Consume k) = \s m. m = point_measure UNIV s) /\
   (rel (Assign v e) = \s m. m = point_measure UNIV (assign v e s)) /\
   (rel (Seq a b) = seq_rel (rel a) (rel b)) /\
   (rel (Nondet a b) = union_rel (rel a) (rel b)) /\
   (rel (Prob p a b) = lin_rel p (rel a r) (rel b r)) /\
   (rel (While c b) = \r. expect_lfp (\e. Cond c (wp b e) r))`;
*)

val _ = export_theory();
