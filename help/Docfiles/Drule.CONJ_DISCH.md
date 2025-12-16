## `CONJ_DISCH`

``` hol4
Drule.CONJ_DISCH : (term -> thm -> thm)
```

------------------------------------------------------------------------

Discharges an assumption and conjoins it to both sides of an equation.

Given an term `t` and a theorem `A |- t1 = t2`, which is an equation
between boolean terms, `CONJ_DISCH` returns
`A - {t} |- (t /\ t1) = (t /\ t2)`, i.e. conjoins `t` to both sides of
the equation, removing `t` from the assumptions if it was there.

``` hol4
            A |- t1 = t2
   ------------------------------  CONJ_DISCH "t"
    A - {t} |- t /\ t1 = t /\ t2
```

### Failure

Fails unless the theorem is an equation, both sides of which, and the
term provided are of type `bool`.

### See also

[`Drule.CONJ_DISCHL`](#Drule.CONJ_DISCHL)
