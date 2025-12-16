## `CHOOSE`

``` hol4
Thm.CHOOSE : term * thm -> thm -> thm
```

------------------------------------------------------------------------

Eliminates existential quantification using deduction from a particular
witness.

When applied to a term-theorem pair `(v,A1 |- ?x. s)` and a second
theorem of the form `A2 u {s[v/x]} |- t`, the inference rule `CHOOSE`
produces the theorem `A1 u A2 |- t`.

``` hol4
    A1 |- ?x. s        A2 u {s[v/x]} |- t
   ---------------------------------------  CHOOSE (v,(A1 |- ?x. s))
                A1 u A2 |- t
```

Where `v` is not free in `A1`, `A2` or `t`.

### Failure

Fails unless the terms and theorems correspond as indicated above; in
particular `v` must have the same type as the variable existentially
quantified over, and must not be free in `A1`, `A2` or `t`.

### See also

[`Tactic.CHOOSE_TAC`](#Tactic.CHOOSE_TAC), [`Thm.EXISTS`](#Thm.EXISTS),
[`Tactic.EXISTS_TAC`](#Tactic.EXISTS_TAC),
[`Drule.SELECT_ELIM`](#Drule.SELECT_ELIM)
