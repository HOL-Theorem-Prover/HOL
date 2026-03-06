## `BOOL_CASES_TAC`

``` hol4
Tactic.BOOL_CASES_TAC : (term -> tactic)
```

------------------------------------------------------------------------

Performs boolean case analysis on a (free) term in the goal.

When applied to a term `x` (which must be of type `bool` but need not be
simply a variable), and a goal `A ?- t`, the tactic `BOOL_CASES_TAC`
generates the two subgoals corresponding to `A ?- t` but with any free
instances of `x` replaced by `F` and `T` respectively.

``` hol4
              A ?- t
   ============================  BOOL_CASES_TAC "x"
    A ?- t[F/x]    A ?- t[T/x]
```

The term given does not have to be free in the goal, but if it isn't,
`BOOL_CASES_TAC` will merely duplicate the original goal twice.

### Failure

Fails unless the term `x` has type `bool`.

### Example

The goal:

``` hol4
   ?- (b ==> ~b) ==> (b ==> a)
```

can be completely solved by using `BOOL_CASES_TAC` on the variable `b`,
then simply rewriting the two subgoals using only the inbuilt
tautologies, i.e. by applying the following tactic:

``` hol4
   BOOL_CASES_TAC (Parse.Term `b:bool`) THEN REWRITE_TAC[]
```

Avoiding fiddly logical proofs by brute-force case analysis, possibly
only over a key term as in the above example, possibly over all free
boolean variables.

### See also

[`Tactic.ASM_CASES_TAC`](#Tactic.ASM_CASES_TAC),
[`Tactic.COND_CASES_TAC`](#Tactic.COND_CASES_TAC),
[`Tactic.DISJ_CASES_TAC`](#Tactic.DISJ_CASES_TAC),
[`Tactic.STRUCT_CASES_TAC`](#Tactic.STRUCT_CASES_TAC)
