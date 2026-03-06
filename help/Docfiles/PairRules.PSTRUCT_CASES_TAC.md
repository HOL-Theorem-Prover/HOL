## `PSTRUCT_CASES_TAC`

``` hol4
PairRules.PSTRUCT_CASES_TAC : thm_tactic
```

------------------------------------------------------------------------

Performs very general structural case analysis.

When it is applied to a theorem of the form:

``` hol4
   th = A' |- ?p11...p1m. (x=t1) /\ (B11 /\ ... /\ B1k) \/ ... \/
                ?pn1...pnp. (x=tn) /\ (Bn1 /\ ... /\ Bnp)
```

in which there may be no paired existential quantifiers where a 'vector'
of them is shown above, `PSTRUCT_CASES_TAC th` splits a goal `A ?- s`
into `n` subgoals as follows:

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
(possibly multiply paired existentially quantified) terms which assert
the equality of the same variable `x` and the given terms.

Generating a case split from the axioms specifying a structure.

### See also

[`Tactic.STRUCT_CASES_TAC`](#Tactic.STRUCT_CASES_TAC)
