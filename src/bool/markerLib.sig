signature markerLib =
sig
  include Abbrev

  val stmark_term : conv

  val stmark_conjunct : (term -> bool) -> conv
  val stmark_disjunct : (term -> bool) -> conv

  val move_stmarked_conj_left : conv
  val move_stmarked_conj_right : conv
  val move_stmarked_disj_left : conv
  val move_stmarked_disj_right : conv

  val move_conj_left : (term -> bool) -> conv
  val move_conj_right : (term -> bool) -> conv
  val move_disj_left : (term -> bool) -> conv
  val move_disj_right : (term -> bool) -> conv
end

(*
   [stmark_term t] wraps term t in a "short term marker".

   [stmark_conjunct P t] finds the first conjunct c amongst the
   conjuncts of term t (conjuncts as returned by strip_conj), for which
   P c returns true and marks it as per stmark_term.  The traversal is
   from left to right.

   [stmark_disjunct P t] finds the first disjunct d amongst the
   disjuncts of term t (disjuncts as returned by strip_disj), for which
   P d returns true and marks it as per stmark_term.  The traversal is
   from left to right.

   [move_stmarked_conj_left t] moves the st-marked conjunct in t to
   the left, so that if t is of the form ... /\ stmark c /\ ..., then
   the returned theorem is of the form
      |- t = c /\ ...
   where c has lost its marker.   The behaviour is undefined if there
   is not exactly one marked conjunct.

   [move_stmarked_conj_right t] moves the st-marked conjunct to the
   right.  Analogous to move_stmarked_conj_left.

   [move_stmarked_disj_left t] moves the st-marked disjunct to the
   left.  Analogous to move_stmarked_conj_left.

   [move_stmarked_disj_right t] moves the st-marked disjunct to the
   right.  Analogous to move_stmarked_conj_left.

   [move_conj_left P t] first looks for a conjunct satisfying P, marks it,
   and then moves it to the left.  Is a composition of stmark_conjunct and
   move_stmarked_conj_left.

   [move_conj_right P t] moves a conjunct satisfying P to the right.
   Analogous to move_conj_left.

   [move_disj_left P t] moves a disjunct satisfying P to the left.
   Analogous to move_conj_left.

   [move_disj_right P t] moves a disjunct satisfying P to the right.
   Analogous to move_conj_left.

*)
