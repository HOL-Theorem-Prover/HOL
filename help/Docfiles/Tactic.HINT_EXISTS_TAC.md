## `HINT_EXISTS_TAC`

``` hol4
Tactic.HINT_EXISTS_TAC : tactic
```

------------------------------------------------------------------------

Reduces an existentially quantified goal by finding a witness which,
from the assumption list, satisfies at least partially the body of the
existential.

When applied to a goal `?x. t1 /\ ... /\ tn`, the tactic
`HINT_EXISTS_TAC` looks for an assumption of the form `ti[u/x]`, where
`i` belongs to `1..n`, and reduces the goal by taking `u` as a witness
for `x`.

### Failure

Fails unless the goal contains an assumption of the expected form.

### Example

- The goal:

  ``` hol4
   b = 0, a < 1, c > 0 ?- ?x. x < 1
  ```

is turned by `HINT_EXISTS_TAC` into:

``` hol4
   b = 0, a < 1, c > 0 ?- a < 1
```

- However the tactic also allows to make progress if only one conjunct
  of the existential is satisfied. For instance, the goal:

  ``` hol4
   b = 0, a < 1, c > 0 ?- ?x. x < 1 /\ x + x = c
  ```

is turned by `HINT_EXISTS_TAC` into:

``` hol4
   b = 0, a < 1, c > 0 ?- a < 1 /\ a + a = c
```

- The location of the conjunct does not matter, the goal:

  ``` hol4
   b = 0, a < 1, c > 0 ?- ?x. x + x = c /\ x < 1
  ```

is turned by `HINT_EXISTS_TAC` into:

``` hol4
   b = 0, a < 1, c > 0 ?- a + a = c /\ a < 1
```

- It can be convenient to chain the call to `HINT_EXISTS_TAC` with one
  to `ASM_REWRITE_TAC` in order to remove automatically the satisfied
  conjunct:

  ``` hol4
   b = 0, a < 1, c > 0 ?- ?x. x + x = c /\ x < 1
  ```

is turned by `HINT_EXISTS_TAC THEN ASM_REWRITE_TAC[]` into:

``` hol4
   b = 0, a < 1, c > 0 ?- a + a = c
```

Avoid providing a witness explicitly, in order to make the tactic script
less fragile.

### See also

[`Tactic.EXISTS_TAC`](#Tactic.EXISTS_TAC)
