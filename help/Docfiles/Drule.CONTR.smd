## `CONTR`

``` hol4
Drule.CONTR : term -> thm -> thm
```

------------------------------------------------------------------------

Implements the intuitionistic contradiction rule.

When applied to a term `t` and a theorem `A |- F`, the inference rule
`CONTR` returns the theorem `A |- t`.

``` hol4
    A |- F
   --------  CONTR t
    A |- t
```

### Failure

Fails unless the term has type `bool` and the theorem has `F` as its
conclusion.

### See also

[`Thm.CCONTR`](#Thm.CCONTR), [`Drule.CONTRAPOS`](#Drule.CONTRAPOS),
[`Tactic.CONTR_TAC`](#Tactic.CONTR_TAC), [`Thm.NOT_ELIM`](#Thm.NOT_ELIM)
