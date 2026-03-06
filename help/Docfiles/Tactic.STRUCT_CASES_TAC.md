## `STRUCT_CASES_TAC`

``` hol4
Tactic.STRUCT_CASES_TAC : thm_tactic
```

------------------------------------------------------------------------

Performs very general structural case analysis.

When it is applied to a theorem of the form:

``` hol4
   th = A' |- ?y11...y1m. (x=t1) /\ (B11 /\ ... /\ B1k) \/ ... \/
                ?yn1...ynp. (x=tn) /\ (Bn1 /\ ... /\ Bnp)
```

in which there may be no existential quantifiers where a 'vector' of
them is shown above, `STRUCT_CASES_TAC th` splits a goal `A ?- s` into
`n` subgoals as follows:

``` hol4
                             A ?- s
   ===============================================================
    A u {B11,...,B1k} ?- s[t1/x] ... A u {Bn1,...,Bnp} ?- s[tn/x]
```

that is, performs a case split over the possible constructions (the
`ti`) of a term, providing as assumptions the given constraints, having
split conjoined constraints into separate assumptions. Note that unless
`A'` is a subset of `A`, this is an invalid tactic.

### Failure

Fails unless the theorem has the above form, namely a conjunction of
(possibly multiply existentially quantified) terms which assert the
equality of the same variable `x` and the given terms.

### Example

Suppose we have the goal:

``` hol4
  ?- ~(l:(*)list = []) ==> (LENGTH l) > 0
```

then we can get rid of the universal quantifier from the inbuilt list
theorem `list_CASES`:

``` hol4
   list_CASES = !l. (l = []) \/ (?t h. l = CONS h t)
```

and then use `STRUCT_CASES_TAC`. This amounts to applying the following
tactic:

``` hol4
   STRUCT_CASES_TAC (SPEC_ALL list_CASES)
```

which results in the following two subgoals:

``` hol4
   ?- ~(CONS h t = []) ==> (LENGTH(CONS h t)) > 0

   ?- ~([] = []) ==> (LENGTH[]) > 0
```

Note that this is a rather simple case, since there are no constraints,
and therefore the resulting subgoals have no assumptions.

Generating a case split from the axioms specifying a structure.

### See also

[`Tactic.ASM_CASES_TAC`](#Tactic.ASM_CASES_TAC),
[`Tactic.BOOL_CASES_TAC`](#Tactic.BOOL_CASES_TAC),
[`Tactic.COND_CASES_TAC`](#Tactic.COND_CASES_TAC),
[`Tactic.DISJ_CASES_TAC`](#Tactic.DISJ_CASES_TAC)
