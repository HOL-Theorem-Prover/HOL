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

val _ = export_theory()
