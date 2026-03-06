## `DISJ2`

``` hol4
Thm.DISJ2 : term -> thm -> thm
```

------------------------------------------------------------------------

Introduces a left disjunct into the conclusion of a theorem.

``` hol4
      A |- t2
   ---------------  DISJ2 "t1"
    A |- t1 \/ t2
```

### Failure

Fails if the term argument is not boolean.

### Example

``` hol4
- DISJ2 F TRUTH;
> val it = |- F \/ T : thm
```

### See also

[`Thm.DISJ1`](#Thm.DISJ1), [`Tactic.DISJ1_TAC`](#Tactic.DISJ1_TAC),
[`Tactic.DISJ2_TAC`](#Tactic.DISJ2_TAC),
[`Thm.DISJ_CASES`](#Thm.DISJ_CASES)
