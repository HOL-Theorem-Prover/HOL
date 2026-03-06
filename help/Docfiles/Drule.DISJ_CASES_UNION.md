## `DISJ_CASES_UNION`

``` hol4
Drule.DISJ_CASES_UNION : thm -> thm -> thm -> thm
```

------------------------------------------------------------------------

Makes an inference for each arm of a disjunct.

Given a disjunctive theorem, and two additional theorems each having one
disjunct as a hypothesis, a new theorem with a conclusion that is the
disjunction of the conclusions of the last two theorems is produced. The
hypotheses include the union of hypotheses of all three theorems less
the two disjuncts.

``` hol4
    A |- t1 \/ t2    A1 u {t1} |- t3     A2 u {t2} |- t4
   ------------------------------------------------------  DISJ_CASES_UNION
                 A u A1 u A2 |- t3 \/ t4
```

### Failure

Fails if the first theorem is not a disjunction.

### Example

The built-in theorem `LESS_CASES` can be specialized to:

``` hol4
   th1 = |- m < n \/ n <= m
```

and used with two additional theorems:

``` hol4
   th2 = (m < n |- (m MOD n = m))
   th3 = ({0 < n, n <= m} |- (m MOD n) = ((m - n) MOD n))
```

to derive a new theorem:

``` hol4
   - DISJ_CASES_UNION th1 th2 th3;
   val it = [0 < n] |- (m MOD n = m) \/ (m MOD n = (m - n) MOD n) : thm
```

### See also

[`Thm.DISJ_CASES`](#Thm.DISJ_CASES),
[`Tactic.DISJ_CASES_TAC`](#Tactic.DISJ_CASES_TAC),
[`Thm.DISJ1`](#Thm.DISJ1), [`Thm.DISJ2`](#Thm.DISJ2)
