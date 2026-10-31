(* HolRefute by case study: a classic two-list queue, adapted in the
   style of Isabelle's Quickcheck_Examples.thy. *)

Theory refuteQueue
Ancestors
  list
Libs
  Refute

Datatype:
  queue = <| front : num list; back : num list |>
End

Definition qrep_def:
  qrep q = q.front ++ REVERSE q.back
End

Definition qinv_def:
  qinv q <=> (q.front = [] ==> q.back = [])
End

Definition qnorm_def:
  qnorm q = if q.front = [] then
              <| front := REVERSE q.back; back := [] |>
            else q
End

Definition qenq0_def:
  qenq0 x q = q with back := x :: q.back
End

Definition qenq_def:
  qenq x q = qnorm (q with back := x :: q.back)
End

Definition qpeek_def:
  qpeek q = case q.front of [] => NONE | x :: _ => SOME x
End

Definition qdeq_def:
  qdeq q = case q.front of
             [] => q
           | _ :: t => qnorm (q with front := t)
End

(* The diagnostic tactic is followed by cheat in deliberately false
   conjectures so that the counterexample remains visible in the build. *)

Theorem the_draft_enqueue_preserves_the_invariant:
  qinv q ==> qinv (qenq0 x q)
Proof
  QUICKCHECK_TAC >> cheat
QED

Theorem peeking_after_a_draft_enqueue_agrees_with_the_abstraction:
  qinv q ==>
  (qpeek (qenq0 x q) = NONE <=> qrep (qenq0 x q) = [])
Proof
  QUICKCHECK_TAC >> cheat
QED

Theorem qrep_qnorm[local]:
  qrep (qnorm q) = qrep q
Proof
  Cases_on `q` >> Cases_on `l` >> simp [qrep_def, qnorm_def,
                                        REVERSE_DEF, APPEND_ASSOC]
QED

Theorem the_fixed_enqueue_preserves_the_invariant:
  qinv q ==> qinv (qenq x q)
Proof
  QUICKCHECK_TAC >>
  Cases_on `q` >> Cases_on `l` >>
  simp [qinv_def, qenq_def, qnorm_def]
QED

Theorem the_fixed_enqueue_appends_to_the_abstraction:
  qrep (qenq x q) = qrep q ++ [x]
Proof
  QUICKCHECK_TAC >>
  Cases_on `q` >> Cases_on `l` >>
  simp [qrep_def, qenq_def, qnorm_def, REVERSE_DEF, APPEND_ASSOC]
QED

Theorem peeking_agrees_with_the_abstraction:
  qinv q ==> (qpeek q = NONE <=> qrep q = [])
Proof
  QUICKCHECK_TAC >>
  Cases_on `q` >> Cases_on `l` >>
  simp [qinv_def, qpeek_def, qrep_def]
QED

Theorem dequeue_drops_the_first_element:
  qinv q ==> qrep (qdeq q) = DROP 1 (qrep q)
Proof
  QUICKCHECK_TAC >>
  Cases_on `q` >> Cases_on `l` >>
  simp [qinv_def, qdeq_def, qnorm_def, qrep_def, REVERSE_DEF,
        DROP_def, APPEND_ASSOC] >>
  Cases_on `t` >>
  simp [qinv_def, qdeq_def, qnorm_def, qrep_def, REVERSE_DEF,
        DROP_def, APPEND_ASSOC]
QED
