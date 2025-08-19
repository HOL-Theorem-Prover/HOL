## `SPEC_UNDISCH_EXL`

``` hol4
Drule.SPEC_UNDISCH_EXL : thm -> thm
```

------------------------------------------------------------------------

Strips universal quantifiers and antecedents of implications (splitting
conjunctive antecedents), then where possible replaces the formerly
quantified variables as existentials in the new hypotheses.

In this example, assume that `a1` and `a3` (only) involve the free
variable `x`.

``` hol4
   |- !x. a1 ==> !y. a2 ==> !z. a3 ==> !u. t
   ----------------------------------------- SPEC_UNDISCH_EXL
       ?x. a1 /\ a3, a2 |- t
```

### Failure

No failure. Can leave the supplied theorem unchanged.

### Comments

See `EXISTS_LEFT` for more on the existential quantification aspect.
Note that the existential quantification happens only for variables
which were universally quantified in the supplied theorem (to get around
this limitation, first apply `GEN_ALL` to the supplied theorem).

### Example

Where `trans_thm` is `[] |- !x y z. (x = y) ==> (y = z) ==> (x = z)`

`SPEC_UNDISCH_EXL trans_thm` is `[?y. (x = y) /\ (y = z)] |- x = z`

### See also

[`Drule.EXISTS_LEFT`](#Drule.EXISTS_LEFT),
[`Tactic.irule`](#Tactic.irule)
