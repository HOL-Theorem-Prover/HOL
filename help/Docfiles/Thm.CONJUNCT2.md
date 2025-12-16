## `CONJUNCT2`

``` hol4
Thm.CONJUNCT2 : thm -> thm
```

------------------------------------------------------------------------

Extracts right conjunct of theorem.

``` hol4
    A |- t1 /\ t2
   ---------------  CONJUNCT2
       A |- t2
```

### Failure

Fails unless the input theorem is a conjunction.

### Comments

The theorem `AND2_THM` can be instantiated to similar effect.

### See also

[`Drule.BODY_CONJUNCTS`](#Drule.BODY_CONJUNCTS),
[`Thm.CONJUNCT1`](#Thm.CONJUNCT1),
[`Drule.CONJ_PAIR`](#Drule.CONJ_PAIR), [`Thm.CONJ`](#Thm.CONJ),
[`Drule.LIST_CONJ`](#Drule.LIST_CONJ),
[`Drule.CONJ_LIST`](#Drule.CONJ_LIST),
[`Drule.CONJUNCTS`](#Drule.CONJUNCTS)
