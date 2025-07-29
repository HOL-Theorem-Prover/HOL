## `SELECT_RULE`

``` hol4
Drule.SELECT_RULE : thm -> thm
```

------------------------------------------------------------------------

Introduces an epsilon term in place of an existential quantifier.

The inference rule `SELECT_RULE` expects a theorem asserting the
existence of a value `x` such that `P` holds. The equivalent assertion
that the epsilon term `@x.P` denotes a value of `x` for which `P` holds
is returned as a theorem.

``` hol4
       A |- ?x. P
   ------------------  SELECT_RULE
    A |- P[(@x.P)/x]
```

### Failure

Fails if applied to a theorem the conclusion of which is not
existentially quantified.

### Example

The axiom `INFINITY_AX` in the theory `ind` is of the form:

``` hol4
   |- ?f. ONE_ONE f /\ ~ONTO f
```

Applying `SELECT_RULE` to this theorem returns the following.

``` hol4
   - SELECT_RULE INFINITY_AX;
   > val it =
     |- ONE_ONE (@f. ONE_ONE f /\ ~ONTO f) /\ ~ONTO @f. ONE_ONE f /\ ~ONTO f
     : thm
```

May be used to introduce an epsilon term to permit rewriting with a
constant defined using the epsilon operator.

### See also

[`Thm.CHOOSE`](#Thm.CHOOSE), [`Conv.SELECT_CONV`](#Conv.SELECT_CONV),
[`Drule.SELECT_ELIM`](#Drule.SELECT_ELIM),
[`Drule.SELECT_INTRO`](#Drule.SELECT_INTRO)
