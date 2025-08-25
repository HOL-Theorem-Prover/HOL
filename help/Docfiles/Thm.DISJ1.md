## `DISJ1`

``` hol4
Thm.DISJ1 : thm -> term -> thm
```

------------------------------------------------------------------------

Introduces a right disjunct into the conclusion of a theorem.

``` hol4
       A |- t1
   ---------------  DISJ1 (A |- t1) t2
    A |- t1 \/ t2
```

### Failure

Fails unless the term argument is boolean.

### Example

``` hol4
- DISJ1 TRUTH F;
> val it = |- T \/ F : thm
```

### See also

[`Tactic.DISJ1_TAC`](#Tactic.DISJ1_TAC), [`Thm.DISJ2`](#Thm.DISJ2),
[`Tactic.DISJ2_TAC`](#Tactic.DISJ2_TAC),
[`Thm.DISJ_CASES`](#Thm.DISJ_CASES)
