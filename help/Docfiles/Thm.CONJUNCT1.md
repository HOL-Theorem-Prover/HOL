## `CONJUNCT1`

``` hol4
Thm.CONJUNCT1 : thm -> thm
```

------------------------------------------------------------------------

Extracts left conjunct of theorem.

``` hol4
    A |- t1 /\ t2
   ---------------  CONJUNCT1
       A |- t1
```

### Failure

Fails unless the input theorem is a conjunction.

### Comments

The theorem `AND1_THM` can be instantiated to similar effect.

### See also

[`Drule.BODY_CONJUNCTS`](#Drule.BODY_CONJUNCTS),
[`Thm.CONJUNCT2`](#Thm.CONJUNCT2),
[`Drule.CONJ_PAIR`](#Drule.CONJ_PAIR), [`Thm.CONJ`](#Thm.CONJ),
[`Drule.LIST_CONJ`](#Drule.LIST_CONJ),
[`Drule.CONJ_LIST`](#Drule.CONJ_LIST),
[`Drule.CONJUNCTS`](#Drule.CONJUNCTS)
