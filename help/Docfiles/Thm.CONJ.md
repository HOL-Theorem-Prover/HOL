## `CONJ`

``` hol4
Thm.CONJ : thm -> thm -> thm
```

------------------------------------------------------------------------

Introduces a conjunction.

``` hol4
    A1 |- t1      A2 |- t2
   ------------------------  CONJ
     A1 u A2 |- t1 /\ t2
```

### Failure

Never fails.

### Comments

The theorem `AND_INTRO_THM` can be instantiated to similar effect.

### See also

[`Drule.BODY_CONJUNCTS`](#Drule.BODY_CONJUNCTS),
[`Thm.CONJUNCT1`](#Thm.CONJUNCT1), [`Thm.CONJUNCT2`](#Thm.CONJUNCT2),
[`Drule.CONJ_PAIR`](#Drule.CONJ_PAIR),
[`Drule.LIST_CONJ`](#Drule.LIST_CONJ),
[`Drule.CONJ_LIST`](#Drule.CONJ_LIST),
[`Drule.CONJUNCTS`](#Drule.CONJUNCTS)
