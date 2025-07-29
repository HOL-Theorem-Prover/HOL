## `LEAST_ELIM_TAC`

``` hol4
numLib.LEAST_ELIM_TAC : tactic
```

------------------------------------------------------------------------

Eliminates a `LEAST` term from the current goal.

`LEAST_ELIM_TAC` searches the goal it is applied to for free sub-terms
involving the `LEAST` operator, of the form `$LEAST P` (`P` will usually
be an abstraction). If such a term is found, the tactic produces a new
goal where instances of the `LEAST`-term have disappeared. The resulting
goal will require the proof that there exists a value satisfying `P`,
and that a minimal value satisfies the original goal.

Thus, `LEAST_ELIM_TAC` can be seen as a higher-order match against the
theorem

``` hol4
   |- !P Q.
         (?n. P x) /\ (!n. (!m. m < n ==> ~P m) /\ P n ==> Q n) ==>
         Q ($LEAST P)
```

where the new goal is the antecdent of the implication. (This theorem is
`LEAST_ELIM`, from theory `while`.)

### Failure

The tactic fails if there is no free `LEAST`-term in the goal.

### Example

When applied to the goal

``` hol4
   ?- (LEAST n. 4 < n) = 5
```

the tactic `LEAST_ELIM_TAC` produces

``` hol4
   ?- (?n. 4 < n) /\ !n. (!m. m < n ==> ~(4 < m)) /\ 4 < n ==> (n = 5)
```

### Comments

This tactic assumes that there is indeed a least number satisfying the
given predicate. If there is not, then the `LEAST`-term will have an
arbitrary value, and the proof should proceed by showing that the
enclosing predicate `Q` holds for all possible numbers.

If there are multiple different `LEAST`-terms in the goal, then
`LEAST_ELIM_TAC` will pick the first free `LEAST`-term returned by the
standard `find_terms` function.

### See also

[`Tactic.DEEP_INTRO_TAC`](#Tactic.DEEP_INTRO_TAC),
[`Tactic.SELECT_ELIM_TAC`](#Tactic.SELECT_ELIM_TAC)
