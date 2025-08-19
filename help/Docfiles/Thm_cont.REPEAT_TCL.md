## `REPEAT_TCL`

``` hol4
Thm_cont.REPEAT_TCL : (thm_tactical -> thm_tactical)
```

------------------------------------------------------------------------

Repeatedly applies a theorem-tactical until it fails when applied to the
theorem.

When applied to a theorem-tactical, a theorem-tactic and a theorem:

``` hol4
   REPEAT_TCL ttl ttac th
```

`REPEAT_TCL` repeatedly modifies the theorem according to `ttl` until it
fails when given to the theorem-tactic `ttac`.

### Failure

Fails iff the theorem-tactic fails immediately when applied to the
theorem.

### Example

It is often desirable to repeat the action of basic theorem-tactics. For
example `CHOOSE_THEN` strips off a single existential quantification, so
one might use `REPEAT_TCL CHOOSE_THEN` to get rid of them all.

Alternatively, one might want to repeatedly break apart a theorem which
is a nested conjunction and apply the same theorem-tactic to each
conjunct. For example the following goal:

``` hol4
   ?- ((0 = w) /\ (0 = x)) /\ (0 = y) /\ (0 = z) ==> (w + x + y + z = 0)
```

might be solved by

``` hol4
   DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
   REWRITE_TAC[ADD_CLAUSES]
```

### See also

[`Thm_cont.REPEAT_GTCL`](#Thm_cont.REPEAT_GTCL),
[`Thm_cont.THEN_TCL`](#Thm_cont.THEN_TCL)
