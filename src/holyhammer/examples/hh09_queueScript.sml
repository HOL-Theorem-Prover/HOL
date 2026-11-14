(* ========================================================================= *)
(* FILE          : hh09_queueScript.sml                                      *)
(* DESCRIPTION   : HolyHammer examples: case study, a functional queue       *)
(*                                                                           *)
(* Every proof below was found by calling the hammer at the point marked     *)
(* (* hh *); the tactic that follows is the verified, minimised proof that   *)
(* HolyHammer printed.  See README.md for how to replay the calls.           *)
(* ========================================================================= *)
Theory hh09_queue
Ancestors
  arithmetic list

(* -------------------------------------------------------------------------
   The classic purely functional queue: a front list f and a reversed
   rear list r.  Elements are pushed onto r and popped from f; when f
   runs out, r is reversed and becomes the new front.  The abstraction
   function qlist gives the list of elements in queue order.

   The lesson of this file: pattern matching and case expressions are
   cheap for the simplifier and expensive for the hammer.  Split the
   cases yourself (Cases_on, CASE_TAC, AllCaseEqs) and let the hammer do
   the reasoning that is left.  Once the operations have been related to
   qlist, everything else is reasoning about lists, where the hammer is
   strong.
   ------------------------------------------------------------------------- *)

Datatype:
  queue = Queue ('a list) ('a list)
End

Definition qlist_def:
  qlist (Queue f r) = f ++ REVERSE r
End

Definition qempty_def:
  qempty = Queue [] []
End

Definition qpush_def:
  qpush x (Queue f r) = Queue f (x::r)
End

Definition qpop_def:
  (qpop (Queue (x::f) r) = SOME (x, Queue f r)) /\
  (qpop (Queue [] r) =
     case REVERSE r of
       [] => NONE
     | x::f => SOME (x, Queue f []))
End

(* -------------------------------------------------------------------------
   Part 1: the operations, related to qlist
   ------------------------------------------------------------------------- *)

Theorem qlist_qempty:
  qlist qempty = []
Proof
  (* hh *)
  metis_tac [qlist_def, qempty_def, APPEND, REVERSE_DEF]
QED

(* The hammer can do a simple case split by itself: it found
   queue_nchotomy, the theorem stored by Datatype that says every queue
   is Queue f r for some f and r. *)
Theorem qlist_qpush:
  qlist (qpush x q) = qlist q ++ [x]
Proof
  (* hh *)
  metis_tac [qpush_def, qlist_def, fetch "hh09_queue" "queue_nchotomy",
             APPEND_ASSOC, REVERSE_DEF]
QED

(* qpop is harder: its definition has a nested pattern match and a case
   expression.  The hammer fails on the whole statement and after
   Cases_on `q` >> Cases_on `l`.  After the definitions are also
   unfolded with simp, the provers find proofs, but Metis cannot replay
   them.  The case expression is what stops it.  CASE_TAC splits on
   REVERSE l0 = [] or REVERSE l0 = h::t, and both remaining goals are
   one-lemma hammer calls:
     REVERSE l0 = []    |-  l0 = []
     REVERSE l0 = h::t  |-  l0 <> []                                     *)
Theorem qpop_none:
  qpop q = NONE <=> qlist q = []
Proof
  Cases_on `q` >> Cases_on `l` >> rw [qpop_def, qlist_def] >> CASE_TAC
  >- (* hh *) metis_tac [REVERSE_EQ_NIL]
  >- (* hh *) metis_tac [REVERSE_DEF, NOT_NIL_CONS]
QED

(* The same recipe for the other direction.  Here the case expression
   is in the assumption qpop q = SOME (x, q'), where CASE_TAC cannot
   reach it.  AllCaseEqs () turns an equation on a case expression into
   a disjunction of the cases, and gvs eliminates the impossible ones:
     REVERSE l0 = x::f  |-  qlist (Queue [] l0) = x::qlist (Queue f [])
                        |-  qlist (Queue (h::t) l0) = h::qlist (Queue t l0)
   Both are hammered from qlist_def and list facts. *)
Theorem qpop_some:
  qpop q = SOME (x, q') ==> qlist q = x :: qlist q'
Proof
  Cases_on `q` >> Cases_on `l` >> rw [qpop_def] >> gvs [AllCaseEqs ()]
  >- (* hh *) metis_tac [qlist_def, APPEND, APPEND_NIL, REVERSE_DEF]
  >- (* hh *) metis_tac [qlist_def, APPEND]
QED

(* -------------------------------------------------------------------------
   Part 2: reasoning about queues through qlist

   From here on, the definitions are not needed: the hammer combines
   the lemmas of part 1 with list facts.
   ------------------------------------------------------------------------- *)

(* A ground instance: no hammer needed, EVAL_TAC computes both sides.
   (The hammer fails on it.) *)
Theorem qpop_qpush_qempty:
  qpop (qpush x qempty) = SOME (x, qempty)
Proof
  EVAL_TAC
QED

Theorem qpush_not_empty:
  qlist q = [] ==> qpop (qpush x q) <> NONE
Proof
  (* hh *)
  metis_tac [qpop_none, qlist_qpush, APPEND, NOT_CONS_NIL]
QED

(* An existential conclusion: the hammer found the theorems saying that
   every option is NONE or SOME y, and every pair is (a, b). *)
Theorem qpop_some_exists:
  qlist q <> [] ==> ?x q'. qpop q = SOME (x, q')
Proof
  (* hh *)
  metis_tac [qpop_none, pairTheory.ABS_PAIR_THM, optionTheory.option_nchotomy]
QED

Theorem qpop_qpush:
  qpop q = SOME (x, q') ==> qlist (qpush y q') = TL (qlist q) ++ [y]
Proof
  (* hh *)
  metis_tac [qlist_qpush, qpop_some, TL_DEF]
QED

Theorem qpop_shrinks:
  qpop q = SOME (x, q') ==> LENGTH (qlist q') < LENGTH (qlist q)
Proof
  (* hh *)
  metis_tac [qpop_some, LENGTH, NOT_LEQ, prim_recTheory.LESS_REFL,
             LESS_CASES]
QED
