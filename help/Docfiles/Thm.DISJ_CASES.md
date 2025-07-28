## `DISJ_CASES` {#Thm.DISJ_CASES}


```
DISJ_CASES : (thm -> thm -> thm -> thm)
```



Eliminates disjunction by cases.


The rule `DISJ_CASES` takes a disjunctive theorem, and two ‘case’
theorems, each with one of the disjuncts as a hypothesis while sharing
alpha-equivalent conclusions.  A new theorem is returned with the same
conclusion as the ‘case’ theorems, and the union of all assumptions
excepting the disjuncts.
    
        A |- t1 \/ t2     A1 u {t1} |- t      A2 u {t2} |- t
       ------------------------------------------------------  DISJ_CASES
                        A u A1 u A2 |- t
    



### Failure

Fails if the first argument is not a disjunctive theorem, or if the
conclusions of the other two theorems are not alpha-convertible.

### Example

Specializing the built-in theorem `num_CASES` gives the theorem:
    
       th = |- (m = 0) \/ (?n. m = SUC n)
    
Using two additional theorems, each having one disjunct as a
hypothesis:
    
       th1 = (m = 0 |- (PRE m = m) = (m = 0))
       th2 = (?n. m = SUC n" |- (PRE m = m) = (m = 0))
    
a new theorem can be derived:
    
       - DISJ_CASES th th1 th2;
       > val it = |- (PRE m = m) = (m = 0) : thm
    



### Comments

Neither of the ‘case’ theorems is required to have either disjunct as a
hypothesis, but otherwise `DISJ_CASES` is pointless.

### See also

[`Tactic.DISJ_CASES_TAC`](#Tactic.DISJ_CASES_TAC), [`Thm_cont.DISJ_CASES_THEN`](#Thm_cont.DISJ_CASES_THEN), [`Thm_cont.DISJ_CASES_THEN2`](#Thm_cont.DISJ_CASES_THEN2), [`Drule.DISJ_CASES_UNION`](#Drule.DISJ_CASES_UNION), [`Thm.DISJ1`](#Thm.DISJ1), [`Thm.DISJ2`](#Thm.DISJ2)

