## `drule` {#Tactic.drule}


```
drule : thm -> tactic
```



Performs one step of resolution (or modus ponens) against implication theorem.


If theorem `th` is of the form `A |- t`, where `t` is of the form
`!x1..xn. P .. /\ ... ==> Q` or `!x1..xn. P .. ==> Q`, then a call to
`drule th (asl,g)` looks for an assumption in `asl` that matches the
pattern `P ..` in `t`. It then performs instantiation of `th`’s
universally quantified and free variables, transforms any conjunctions
on the left into a minimal number of chained implications, and calls
`MP` once to generate a consequent theorem `A |- t'`. This theorem is
then passed to `MP_TAC`, turning the goal into `(asl, t' ==> g)`. (We
assume that `A` is a subset of `asl`; otherwise the tactic is
invalid.)

### Failure

A call to `drule th (asl,g)` will fail if `th` is not a (possibly
universally quantified) implication (or negation), or if there are no
assumptions in `asl` matching the “first” hypothesis of `th`.

### Example

The `DIV_LESS` theorem states:
    
       !n d. 0 < n /\ 1 < d ==> (n DIV d < n)
    
Then:
    
       > drule arithmeticTheory.DIV_LESS ([“1 < x”, “0 < y”], “P:bool”);
       val it =
          ([([“1 < x”, “0 < y”], “(!d. 1 < d ==> y DIV d < y) ==> P”)], fn):
          goal list * validation
    

### Comments

The `drule` tactic is similar to, but a great deal more controlled
than, the `IMP_RES_TAC` tactic, which will look for a great many more
possible instantiations and resolutions to perform. `IMP_RES_TAC` also
puts all of its derived consequences into the assumption list; `drule`
can be sure that there will be just one such consequence, and puts
this into the goal directly.

The related `dxrule` tactic removes the matching assumption from the
assumption list. In this example above, the resulting assumption list
would just contain `1 < x`, having lost the `0 < y` which was
resolved against the `DIV_LESS` theorem.

The `drule` tactic uses the `MP_TAC` `thm_tactic` as its fixed
continuation; the `drule_then` variation takes a `thm_tactic`
continuation as its first parameter and applies this to the result of
the instantiation and `MP` call. There is also a `dxrule_then`, that
combines both variations described here.

Finally, note that the implicational theorem may itself have come from
the goal’s assumptions, extracted with tools such as `FIRST_ASSUM` and
`PAT_ASSUM`.

### See also

[`Tactic.drule_all`](#Tactic.drule_all), [`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC)

