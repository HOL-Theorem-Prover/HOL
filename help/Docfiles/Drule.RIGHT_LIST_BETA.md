## `RIGHT_LIST_BETA` {#Drule.RIGHT_LIST_BETA}


```
RIGHT_LIST_BETA : (thm -> thm)
```



Iteratively beta-reduces a top-level beta-redex on the right-hand side of an
equation.


When applied to an equational theorem, `RIGHT_LIST_BETA` applies beta-reduction
over a top-level chain of beta-redexes to the right hand side (only). Variables
are renamed if necessary to avoid free variable capture.
    
        A |- s = (\x1...xn. t) t1 ... tn
       ----------------------------------  RIGHT_LIST_BETA
           A |- s = t[t1/x1]...[tn/xn]
    



### Failure

Fails unless the theorem is equational, with its right-hand side being
a top-level beta-redex.

### See also

[`Thm.BETA_CONV`](#Thm.BETA_CONV), [`Conv.BETA_RULE`](#Conv.BETA_RULE), [`Tactic.BETA_TAC`](#Tactic.BETA_TAC), [`Drule.LIST_BETA_CONV`](#Drule.LIST_BETA_CONV), [`Drule.RIGHT_BETA`](#Drule.RIGHT_BETA)

