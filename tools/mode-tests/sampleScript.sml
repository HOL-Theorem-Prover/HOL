open foobar

val _ = new_theory "foobar";

Theorem foo0 = TRUTH
Theorem foo = TRUTH

Theorem bar: x = x
Proof simp[]
QED

Type x = “:bool”

Definition foo:
  foo x = x + 2
End

Theorem foo:
  x = x
Proof
  all_tac
QED

Definition bar:
  bar x y ⇔
  ∀z.
    x + z < y + z ∧ let a = 2 * x ;
                        b = 3 * z
                    in
                      a * b ≤ x
End

Theorem baz:
  x ∧ let
    a = b;
    c = d;
  in
    x ⇒ a ∧
        c
Proof
  some_tactic
QED

Theorem ifindent1:
  p = if x = 3 then
        10
      else
        14
Proof
  another_tactic ‘quotation arg’
QED

Theorem ifindent2:
  p = if x = 3 then
        10
      else if x = 10 then
        14
      else 16
Proof
  another_tactic ‘quotation arg’
QED

Theorem caseindent1:
  p ⇒ case x of
      | y =>
          z + y + long expression
      | a => something
Proof
  tactic
QED

Theorem caseindent2:
  p ⇒ case x of
        y =>
          z + y + long expression
      | a => something
      | b => last thing ∧
             something
Proof
  tactic
QED

Theorem doindent1:
  do
    x <- e1;
    y <- e2;
  od
Proof
  foo
QED

Theorem first_suffices_by_indent:
  some_asm ∧ p ⇒
  some_goal
Proof
  ‘a long ∧ statement of a ∧ simple subgoal’
    suffices_by atactic >>
  finishing_tactic
QED

Theorem first_by_indent:
  some_goal
Proof
  ‘some other goal’
    by atactic >>
  finishing_tactic
QED

Theorem later_suffices_by_by_indent:
  some_goal
Proof
  tac1 >>
  ‘goal’
    suffices_by foo >>
  ‘goal2’ suffices_by
    bar >>
  ‘goal3’
    by foo >>
  ‘goal4’ by
    foo >>
  finisher
  >> ‘goal4’
    by foobar >>
  ‘goal5’
    by (‘subgoal1’
          suffices_by tac >>
        ‘subgoal2’
          by another_tac) >>
  finisher
QED

Theorem alpha_qfier_and_blashthen:
  (LEAST n. p ∧ q n ⇒
            r n)
  =
  10
Proof
  tac \\
  tac2
QED

(* escaped_alpha_qfier *)
val t =  “P $some ∧ x < y ∧
          Q”;

(* escaped symbol qfier *)
val t = “P $@ ∧
         q”

Theorem eval_op_later:
  eval_op f vs s = (res,t) ⇒ s ≤ t
Proof
  fs [eval_op_def, AllCaseEqs(),fail_def,return_def] \\ rw[]
  \\ fs[later_refl] \\ fs{later_def]
  \\ Cases_on ‘s.input’ \\ fs[forward_def,greater_def]
QED

val _ = export_theory()
