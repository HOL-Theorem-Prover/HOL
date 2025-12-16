## `LIST_CONJ`

``` hol4
Drule.LIST_CONJ : thm list -> thm
```

------------------------------------------------------------------------

Conjoins the conclusions of a list of theorems.

``` hol4
         A1 |- t1 ... An |- tn
   ----------------------------------  LIST_CONJ
    A1 u ... u An |- t1 /\ ... /\ tn
```

### Failure

`LIST_CONJ` fails if applied to an empty list of theorems.

### See also

[`Drule.BODY_CONJUNCTS`](#Drule.BODY_CONJUNCTS),
[`Thm.CONJ`](#Thm.CONJ), [`Thm.CONJUNCT1`](#Thm.CONJUNCT1),
[`Thm.CONJUNCT2`](#Thm.CONJUNCT2),
[`Drule.CONJUNCTS`](#Drule.CONJUNCTS),
[`Drule.CONJ_PAIR`](#Drule.CONJ_PAIR),
[`Tactic.CONJ_TAC`](#Tactic.CONJ_TAC)
