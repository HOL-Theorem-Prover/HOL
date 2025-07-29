## `CONJ_PAIR`

``` hol4
Drule.CONJ_PAIR : thm -> thm * thm
```

------------------------------------------------------------------------

Extracts both conjuncts of a conjunction.

``` hol4
       A |- t1 /\ t2
   ----------------------  CONJ_PAIR
    A |- t1      A |- t2
```

The two resultant theorems are returned as a pair.

### Failure

Fails if the input theorem is not a conjunction.

### See also

[`Drule.BODY_CONJUNCTS`](#Drule.BODY_CONJUNCTS),
[`Thm.CONJUNCT1`](#Thm.CONJUNCT1), [`Thm.CONJUNCT2`](#Thm.CONJUNCT2),
[`Thm.CONJ`](#Thm.CONJ), [`Drule.LIST_CONJ`](#Drule.LIST_CONJ),
[`Drule.CONJ_LIST`](#Drule.CONJ_LIST),
[`Drule.CONJUNCTS`](#Drule.CONJUNCTS)
