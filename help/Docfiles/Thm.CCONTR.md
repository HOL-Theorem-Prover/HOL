## `CCONTR`

``` hol4
Thm.CCONTR : term -> thm -> thm
```

------------------------------------------------------------------------

Implements the classical contradiction rule.

When applied to a term `t` and a theorem `A |- F`, the inference rule
`CCONTR` returns the theorem `A - {~t} |- t`.

``` hol4
       A |- F
   ---------------  CCONTR t
    A - {~t} |- t
```

### Failure

Fails unless the term has type `bool` and the theorem has `F` as its
conclusion.

### Comments

The usual use will be when `~t` exists in the assumption list; in this
case, `CCONTR` corresponds to the classical contradiction rule: if `~t`
leads to a contradiction, then `t` must be true.

### See also

[`Drule.CONTR`](#Drule.CONTR), [`Drule.CONTRAPOS`](#Drule.CONTRAPOS),
[`Tactic.CONTR_TAC`](#Tactic.CONTR_TAC), [`Thm.NOT_ELIM`](#Thm.NOT_ELIM)
