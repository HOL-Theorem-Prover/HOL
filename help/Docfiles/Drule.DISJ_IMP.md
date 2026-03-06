## `DISJ_IMP`

``` hol4
Drule.DISJ_IMP : (thm -> thm)
```

------------------------------------------------------------------------

Converts a disjunctive theorem to an equivalent implicative theorem.

The left disjunct of a disjunctive theorem becomes the negated
antecedent of the newly generated theorem.

``` hol4
     A |- t1 \/ t2
   -----------------  DISJ_IMP
    A |- ~t1 ==> t2
```

### Failure

Fails if the theorem is not a disjunction.

### Example

Specializing the built-in theorem `LESS_CASES` gives the theorem:

``` hol4
   th = |- m < n \/ n <= m
```

to which `DISJ_IMP` may be applied:

``` hol4
   - DISJ_IMP th;
   > val it = |- ~m < n ==> n <= m : thm
```

### See also

[`Thm.DISJ_CASES`](#Thm.DISJ_CASES)
