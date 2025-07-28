## `X_CASES_THENL` {#Thm_cont.X_CASES_THENL}


```
X_CASES_THENL : term list list -> thm_tactic list -> thm_tactic
```



Applies theorem-tactics to corresponding disjuncts of a theorem, choosing
witnesses.


Let `[yl1,...,yln]` represent a list of variable lists, each of length zero or
more, and `xl1,...,xln` each represent a vector of zero or more variables, so
that the variables in each of `yl1...yln` have the same types as the
corresponding `xli`. The function `X_CASES_THENL` expects a list of variable
lists, `[yl1,...,yln]`, a list of tactic-generating functions
`[f1,...,fn]:(thm->tactic)list`, and a disjunctive theorem, where each disjunct
may be existentially quantified:
    
       th = |-(?xl1.B1)  \/...\/  (?xln.Bn)
    
each disjunct having the form `(?xi1 ... xim. Bi)`. If applying each
`fi` to the theorem obtained by introducing witness variables `yli` for the
objects `xli` whose existence is asserted by the `i`th disjunct,
`({Bi[yli/xli]} |- Bi[yli/xli])`, produces the following results when applied
to a goal `(A ?- t)`:
    
        A ?- t
       =========  f1 ({B1[yl1/xl1]} |- B1[yl1/xl1])
        A ?- t1
    
        ...
    
        A ?- t
       =========  fn ({Bn[yln/xln]} |- Bn[yln/xln])
        A ?- tn
    
then applying `X_CASES_THENL [yl1,...,yln] [f1,...,fn] th`
to the goal `(A ?- t)` produces `n` subgoals.
    
               A ?- t
       =======================  X_CASES_THENL [yl1,...,yln] [f1,...,fn] th
        A ?- t1  ...  A ?- tn
    



### Failure

Fails (with `X_CASES_THENL`) if any `yli` has more variables than the
corresponding `xli`, or (with `SUBST`) if corresponding variables have
different types, or (with `combine`) if the number of theorem tactics
differs from the number of disjuncts.  Failures may arise in the
tactic-generating function.  An invalid tactic is produced if any
variable in any of the `yli` is free in the corresponding `Bi` or in
`t`, or if the theorem has any hypothesis which is not
alpha-convertible to an assumption of the goal.

### Example

Given the goal `?- (x MOD 2) <= 1`, the following theorem may be
used to split into 2 cases:
    
       th = |- (?m. x = 2 * m) \/ (?m. x = (2 * m) + 1)
    
by the tactic
    
       X_CASES_THENL [[Term`n:num`], [Term`n:num`]] [ASSUME_TAC, SUBST1_TAC] th
    
to produce the subgoals:
    
       ?- (((2 * n) + 1) MOD 2) <= 1
    
       {x = 2 * n} ?- (x MOD 2) <= 1
    



### See also

[`Thm_cont.DISJ_CASES_THEN`](#Thm_cont.DISJ_CASES_THEN), [`Thm_cont.X_CASES_THEN`](#Thm_cont.X_CASES_THEN), [`Thm_cont.X_CHOOSE_THEN`](#Thm_cont.X_CHOOSE_THEN)

