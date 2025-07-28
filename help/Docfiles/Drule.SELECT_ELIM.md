## `SELECT_ELIM` {#Drule.SELECT_ELIM}


```
SELECT_ELIM : thm -> term * thm -> thm
```



Eliminates an epsilon term, using deduction from a particular instance.


`SELECT_ELIM` expects two arguments, a theorem `th1`, and a pair
`(v,th2): term * thm`.  The conclusion of `th1` should have the form
`P($@ P)`, which asserts that the epsilon term `$@ P` denotes some
value at which `P` holds.  In `th2`, the variable `v` appears only in
the assumption `P v`.  The conclusion of the resulting theorem matches
that of `th2`, and the hypotheses include the union of all hypotheses
of the premises excepting `P v`.
    
        A1 |- P($@ P)     A2 u {P v} |- t
       -----------------------------------  SELECT_ELIM th1 (v,th2)
                  A1 u A2 |- t
    
where `v` is not free in `A2`. The argument to `P` in the conclusion
of `th1` may actually be any term `x`.  If `v` appears in the
conclusion of `th2`, this argument `x` (usually the epsilon term) will
NOT be eliminated, and the conclusion will be `t[x/v]`.

### Failure

Fails if the first theorem is not of the form `A1 |- P x`, or if
the variable `v` occurs free in any other assumption of `th2`.

### Example

If a property of functions is defined by:
    
       INCR = |- !f. INCR f = (!t1 t2. t1 < t2 ==> (f t1) < (f t2))
    
The following theorem can be proved.
    
       th1 = |- INCR(@f. INCR f)
    
Additionally, if such a function is assumed to exist, then one
can prove that there also exists a function which is injective (one-to-one) but
not surjective (onto).
    
       th2 = [ INCR g ] |- ?h. ONE_ONE h /\ ~ONTO h
    
These two results may be combined using `SELECT_ELIM` to
give a new theorem:
    
       - SELECT_ELIM th1 (``g:num->num``, th2);
       val it = |- ?h. ONE_ONE h /\ ~ONTO h : thm
    




This rule is rarely used.  The equivalence of `P($@ P)` and `$? P`
makes this rule fundamentally similar to the `?`-elimination rule `CHOOSE`.

### See also

[`Thm.CHOOSE`](#Thm.CHOOSE), [`Conv.SELECT_CONV`](#Conv.SELECT_CONV), [`Tactic.SELECT_ELIM_TAC`](#Tactic.SELECT_ELIM_TAC), [`Drule.SELECT_INTRO`](#Drule.SELECT_INTRO), [`Drule.SELECT_RULE`](#Drule.SELECT_RULE)

