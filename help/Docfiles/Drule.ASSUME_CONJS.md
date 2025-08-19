## `ASSUME_CONJS`

``` hol4
Drule.ASSUME_CONJS : term -> thm
```

------------------------------------------------------------------------

Constructs a theorem proving a conjunction from its individual conjuncts

Takes a term which should be a conjunction, and returns a theorem whose
hypotheses are the individual conjuncts, and whose conclusion is the
argument term, the conjunction.

### Failure

Never fails.

### Example

``` ASSUME_CONJS (``t1 /\ t2 /\ ... /\ tn``) ``` returns
`[t1, t2, ..., tn] |- t1 /\ t2 /\ ... /\ tn`

To split up conjuncts in selected hypotheses `hyps` of a theorem `th`,
use `Lib.itlist (PROVE_HYP o ASSUME_CONJS) hyps th`

### See also

[`Drule.CONJUNCTS`](#Drule.CONJUNCTS), [`Thm.CONJ`](#Thm.CONJ),
[`Drule.CONJUNCTS_AC`](#Drule.CONJUNCTS_AC),
[`Drule.UNDISCH_SPLIT`](#Drule.UNDISCH_SPLIT)
