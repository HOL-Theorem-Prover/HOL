## `CHOOSE_TAC`

``` hol4
Tactic.CHOOSE_TAC : thm_tactic
```

------------------------------------------------------------------------

Adds the body of an existentially quantified theorem to the assumptions
of a goal.

When applied to a theorem `A' |- ?x. t` and a goal, `CHOOSE_TAC` adds
`t[x'/x]` to the assumptions of the goal, where `x'` is a variant of `x`
which is not free in the goal or assumption list; normally `x'` is just
`x`.

``` hol4
         A ?- u
   ====================  CHOOSE_TAC (A' |- ?x. t)
    A u {t[x'/x]} ?- u
```

Unless `A'` is a subset of `A`, this is not a valid tactic.

### Failure

Fails unless the given theorem is existentially quantified.

### Example

Suppose we have a goal asserting that the output of an electrical
circuit (represented as a boolean-valued function) will become high at
some time:

``` hol4
   ?- ?t. output(t)
```

and we have the following theorems available:

``` hol4
   t1 = |- ?t. input(t)
   t2 = !t. input(t) ==> output(t+1)
```

Then the goal can be solved by the application of:

``` hol4
   CHOOSE_TAC th1
     THEN EXISTS_TAC (Term `t+1`)
     THEN UNDISCH_TAC (Term `input (t:num) :bool`)
     THEN MATCH_ACCEPT_TAC th2
```

### Comments

To do similarly with several existentially quantified variables, use
`REPEAT_TCL CHOOSE_THEN ASSUME_TAC` in place of `CHOOSE_TAC`

### See also

[`Thm_cont.CHOOSE_THEN`](#Thm_cont.CHOOSE_THEN),
[`Tactic.X_CHOOSE_TAC`](#Tactic.X_CHOOSE_TAC),
[`Thm_cont.REPEAT_TCL`](#Thm_cont.REPEAT_TCL)
