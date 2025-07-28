## `CASES_THENL` {#Thm_cont.CASES_THENL}


```
CASES_THENL : (thm_tactic list -> thm_tactic)
```



Applies the theorem-tactics in a list to corresponding disjuncts in a theorem.


When given a list of theorem-tactics `[ttac1;...;ttacn]` and a theorem whose
conclusion is a top-level disjunction of `n` terms, `CASES_THENL` splits a goal
into `n` subgoals resulting from applying to the original goal the result of
applying the `i`’th theorem-tactic to the `i`’th disjunct. This can be
represented as follows, where the number of existentially quantified variables
in a disjunct may be zero. If the theorem `th` has the form:
    
       A' |- ?x11..x1m. t1 \/ ... \/ ?xn1..xnp. tn
    
where the number of existential quantifiers may be zero,
and for all `i` from `1` to `n`:
    
         A ?- s
       ========== ttaci (|- ti[xi1'/xi1]..[xim'/xim])
        Ai ?- si
    
where the primed variables have the same type as their unprimed
counterparts, then:
    
                 A ?- s
       =========================  CASES_THENL [ttac1;...;ttacn] th
        A1 ?- s1  ...  An ?- sn
    
Unless `A'` is a subset of `A`, this is an invalid tactic.

### Failure

Fails if the given theorem does not, at the top level,
have the same number of (possibly multiply existentially quantified) disjuncts
as the length of the theorem-tactic list (this includes the case where the
theorem-tactic list is empty), or if any of the tactics generated as specified
above fail when applied to the goal.


Performing very general disjunctive case splits.

### See also

[`Thm_cont.DISJ_CASES_THENL`](#Thm_cont.DISJ_CASES_THENL), [`Thm_cont.X_CASES_THENL`](#Thm_cont.X_CASES_THENL)

