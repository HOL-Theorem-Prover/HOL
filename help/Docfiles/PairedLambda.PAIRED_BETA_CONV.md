## `PAIRED_BETA_CONV` {#PairedLambda.PAIRED_BETA_CONV}


```
PAIRED_BETA_CONV : conv
```



Performs generalized beta conversion for tupled beta-redexes.


The conversion `PAIRED_BETA_CONV` implements beta-reduction for certain
applications of tupled lambda abstractions called ‘tupled beta-redexes’.
Tupled lambda abstractions have the form `\<vs>.tm`, where `<vs>` is an
arbitrarily-nested tuple of variables called a ‘varstruct’. For the
purposes of `PAIRED_BETA_CONV`, the syntax of varstructs is given by:
    
       <vs>  ::=   (v1,v2)  |  (<vs>,v)  |  (v,<vs>)  |  (<vs>,<vs>)
    
where `v`, `v1`, and `v2` range over variables.  A tupled beta-redex
is an application of the form `(\<vs>.tm) t`, where the term `t` is a
nested tuple of values having the same structure as the varstruct `<vs>`. For
example, the term:
    
       (\((a,b),(c,d)). a + b + c + d)  ((1,2),(3,4))
    
is a tupled beta-redex, but the term:
    
       (\((a,b),(c,d)). a + b + c + d)  ((1,2),p)
    
is not, since `p` is not a pair of terms.

Given a tupled beta-redex `(\<vs>.tm) t`, the conversion `PAIRED_BETA_CONV`
performs generalized beta-reduction and returns the theorem
    
       |-  (\<vs>.tm) t = t[t1,...,tn/v1,...,vn]
    
where `ti` is the subterm of the tuple `t` that corresponds to
the variable `vi` in the varstruct `<vs>`. In the simplest case, the
varstruct `<vs>` is flat, as in the term:
    
       (\(v1,...,vn).t) (t1,...,tn)
    
When applied to a term of this form, `PAIRED_BETA_CONV` returns:
    
       |- (\(v1, ... ,vn).t) (t1, ... ,tn) = t[t1,...,tn/v1,...,vn]
    
As with ordinary beta-conversion, bound variables may be renamed to
prevent free variable capture.  That is, the term `t[t1,...,tn/v1,...,vn]` in
this theorem is the result of substituting `ti` for `vi` in parallel in `t`,
with suitable renaming of variables to prevent free variables in `t1`, ...,
`tn` becoming bound in the result.

### Failure

`PAIRED_BETA_CONV tm` fails if `tm` is not a tupled beta-redex, as described
above.  Note that ordinary beta-redexes are specifically excluded:
`PAIRED_BETA_CONV` fails when applied to `(\v.t)u`.  For these beta-redexes,
use `BETA_CONV`, or `GEN_BETA_CONV`.

### Example

The following is a typical use of the conversion:
    
       - PairedLambda.PAIRED_BETA_CONV
            (Term `(\((a,b),(c,d)). a + b + c + d)  ((1,2),(3,4))`);
       > val it = |- (\((a,b),c,d). a+b+c+d) ((1,2),3,4) = 1+2+3+4 : thm
    
Note that the term to which the tupled lambda abstraction
is applied must have the same structure as the varstruct.  For example,
the following succeeds:
    
       - PairedLambda.PAIRED_BETA_CONV
             (Term `(\((a,b),p). a + b)  ((1,2),(3+5,4))`);
       > val it = |- (\((a,b),p). a + b)((1,2),3 + 5,4) = 1 + 2 : thm
    
but the following call fails:
    
       - PairedLambda.PAIRED_BETA_CONV
           (Term `(\((a,b),(c,d)). a + b + c + d)  ((1,2),p)`);
       ! Uncaught exception:
       ! HOL_ERR
    
because `p` is not a pair.

### See also

[`Thm.BETA_CONV`](#Thm.BETA_CONV), [`Conv.BETA_RULE`](#Conv.BETA_RULE), [`Tactic.BETA_TAC`](#Tactic.BETA_TAC), [`Drule.LIST_BETA_CONV`](#Drule.LIST_BETA_CONV), [`Drule.RIGHT_BETA`](#Drule.RIGHT_BETA), [`Drule.RIGHT_LIST_BETA`](#Drule.RIGHT_LIST_BETA)

