## `REFINE_EXISTS_TAC`

``` hol4
Q.REFINE_EXISTS_TAC : term quotation -> tactic
```

------------------------------------------------------------------------

Attacks existential goals, making the existential variable more
concrete.

The tactic `Q.REFINE_EXISTS_TAC q` parses the quotation `q` in the
context of the (necessarily existential) goal to which it is applied,
and uses the resulting term as the witness for the goal. However, if the
witness has any variables not already present in the goal, then these
are treated as new existentially quantified variables. If there are no
such "free" variables, then the behaviour is the same as `EXISTS_TAC`.

### Failure

Fails if the goal is not existential, or if the quotation can not parse
to a term of the same type as the existentially quantified variable.

### Example

If the quotation doesn't mention any new variables:

``` hol4
   - Q.REFINE_EXISTS_TAC `n` ([``n > x``], ``?m. m > x``);
   > val it =
       ([([``n > x``], ``n > x``)], fn)
       : (term list * term) list * (thm list -> thm)
```

If the quotation does mention any new variables, they are existentially
quantified in the new goal:

``` hol4
   - Q.REFINE_EXISTS_TAC `n + 2` ([``~P 0``], ``?p. P (p - 1)``);
   > val it =
       ([([``~P 0``], ``?n. P (n + 2 - 1)``)], fn)
       : (term list * term) list * (thm list -> thm)
```

`Q.REFINE_EXISTS_TAC` is useful if it is clear that an existential goal
will be solved by a term of particular form, while it is not yet clear
precisely what term this will be. Further proof activity should be able
to exploit the additional structure that has appeared in the place of
the existential variable.

### See also

[`Q.LIST_REFINE_EXISTS_TAC`](#Q.LIST_REFINE_EXISTS_TAC),
[`Tactic.EXISTS_TAC`](#Tactic.EXISTS_TAC)
