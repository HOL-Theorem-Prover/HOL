## `MATCH_ABBREV_TAC` {#Q.MATCH_ABBREV_TAC}


```
Q.MATCH_ABBREV_TAC : term quotation -> tactic
```



Introduces abbreviations by matching a pattern against the goal statement.


When applied to the goal `(asl, w)`, the tactic `Q.MATCH_ABBREV_TAC q`
parses the quotation `q` in the context of the goal, producing a term
to use as a pattern.  The tactic then attempts a (first order) match
of the pattern against the term `w`.  Variables that occur in both the
pattern and the goal are treated as “local constants”, and will not
acquire instantiations.

For each variable `v` in the pattern that has not been treated as a
local constant, there will be an instantiation term `t`, such that the
substitution pattern `[v1 |-> t1, v2 |-> t2, ...]` produces `w`. The
effect of the tactic is to then perform abbreviations in the goal,
replacing each `t` with the corresponding `v` (as long as `v` does not
have a name beginning with an underscore character), and adding
assumptions of the form `Abbrev(v = t)` to the goal.

Because the tactic ignores underscore variables, the user can
abbreviate just those parts of the goal that are particularly
relevant. Note also that the standard parser treats variables
consisting of entirely underscores specially: each is expanded to a
fresh name. This means that a pattern can use `_` repeatedly, and it
will not cause the match to look for the same instantiation for each
occurrence. Nor it will require corresponding sub-terms to have the
same type.

### Failure

`MATCH_ABBREV_TAC` fails if the pattern provided does not match the
goal, or if variables from the goal are used in the pattern in ways
that make the pattern fail to type-check.

### Example

If the current goal is
    
       ?- (n + 10) * y <= 42315 /\ (!x y. x < y ==> f x < f y)
    
then applying the tactic `` Q.MATCH_ABBREV_TAC `X <= Y /\ P` `` results in
the goal
    
       Abbrev(X = (n + 10) * y),
       Abbrev(Y = 42315),
       Abbrev(P = !x y. x < y ==> f x < f y)
          ?-
       X <= Y /\ P
    
If the current goal is
    
       ?- (n + 10) * y <= 42315 /\ (!x y. x < y ==> f x < f y)
    
then applying the tactic `` Q.MATCH_ABBREV_TAC `a * _ <= b /\ _` `` results in
the goal
    
       Abbrev (a = n + 10)
       Abbrev (b = 42315)
         ?-
       a * y <= b /\ !x y. x < y ==> f x < f y
    



### See also

[`Q.ABBREV_TAC`](#Q.ABBREV_TAC), [`Q.HO_MATCH_ABBREV_TAC`](#Q.HO_MATCH_ABBREV_TAC)

