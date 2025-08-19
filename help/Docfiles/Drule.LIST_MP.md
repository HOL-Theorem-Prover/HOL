## `LIST_MP`

``` hol4
Drule.LIST_MP : thm list -> thm -> thm
```

------------------------------------------------------------------------

Performs a chain of Modus Ponens inferences.

When applied to theorems `A1 |- t1, ..., An |- tn` and a theorem which
is a chain of implications with the successive antecedents the same as
the conclusions of the theorems in the list (up to alpha-conversion),
`A |- t1 ==> ... ==> tn ==> t`, the `LIST_MP` inference rule performs a
chain of `MP` inferences to deduce `A u A1 u ... u An |- t`.

``` hol4
    A1 |- t1 ... An |- tn      A |- t1 ==> ... ==> tn ==> t
   ---------------------------------------------------------  LIST_MP
                    A u A1 u ... u An |- t
```

### Failure

Fails unless the theorem is a chain of implications whose consequents
are the same as the conclusions of the list of theorems (up to
alpha-conversion), in sequence.

### See also

[`Thm.EQ_MP`](#Thm.EQ_MP), [`Drule.MATCH_MP`](#Drule.MATCH_MP),
[`Tactic.MATCH_MP_TAC`](#Tactic.MATCH_MP_TAC), [`Thm.MP`](#Thm.MP),
[`Tactic.MP_TAC`](#Tactic.MP_TAC)
