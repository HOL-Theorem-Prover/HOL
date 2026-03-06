## `PMATCH_MP`

``` hol4
PairRules.PMATCH_MP : (thm -> thm -> thm)
```

------------------------------------------------------------------------

Modus Ponens inference rule with automatic matching.

When applied to theorems `A1 |- !p1...pn. t1 ==> t2` and `A2 |- t1'`,
the inference rule `PMATCH_MP` matches `t1` to `t1'` by instantiating
free or paired universally quantified variables in the first theorem
(only), and returns a theorem `A1 u A2 |- !pa..pk. t2'`, where `t2'` is
a correspondingly instantiated version of `t2`. Polymorphic types are
also instantiated if necessary.

Variables free in the consequent but not the antecedent of the first
argument theorem will be replaced by variants if this is necessary to
maintain the full generality of the theorem, and any pairs which were
universally quantified over in the first argument theorem will be
universally quantified over in the result, and in the same order.

``` hol4
    A1 |- !p1..pn. t1 ==> t2   A2 |- t1'
   --------------------------------------  MATCH_MP
          A1 u A2 |- !pa..pk. t2'
```

### Failure

Fails unless the first theorem is a (possibly repeatedly paired
universally quantified) implication whose antecedent can be instantiated
to match the conclusion of the second theorem, without instantiating any
variables which are free in `A1`, the first theorem's assumption list.

### See also

[`Drule.MATCH_MP`](#Drule.MATCH_MP)
