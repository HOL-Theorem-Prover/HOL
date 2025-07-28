## `SUBST_CONV` {#Drule.SUBST_CONV}


```
SUBST_CONV : {redex :term, residue :thm} list -> term -> conv
```



Makes substitutions in a term at selected occurrences of subterms, using a list
of theorems.


`SUBST_CONV` implements the following rule of simultaneous substitution
    
                        A1 |- t1 = v1 ... An |- tn = vn
       ------------------------------------------------------------------
        A1 u ... u An |- t[t1,...,tn/x1,...,xn] = t[v1,...,vn/x1,...,xn]
    
The first argument to `SUBST_CONV` is a list
`[{redex=x1, residue = A1|-t1=v1},...,{redex = xn, residue = An|-tn=vn}]`.
The second argument is a template term `t[x1,...,xn]`, in which
the variables `x1,...,xn` are used to mark those places where
occurrences of `t1,...,tn` are to be replaced with the terms
`v1,...,vn`, respectively.
Thus, evaluating
    
       SUBST_CONV [{redex = x1, residue = A1|-t1=v1},...,
                   {redex = xn, residue = An|-tn=vn}]
                  t[x1,...,xn]
                  t[t1,...,tn/x1,...,xn]
    
returns the theorem
    
       A1 u ... u An |- t[t1,...,tn/x1,...,xn] = t[v1,...,vn/x1,...,xn]
    

The occurrence of `ti` at the places marked by the variable
`xi` must be free (i.e. `ti` must not contain any bound variables).
`SUBST_CONV` automatically renames bound variables to prevent free
variables in `vi` becoming bound after substitution.



### Failure

`SUBST_CONV [{redex=x1,residue=th1},...,{redex=xn,residue=thn}] t[x1,...,xn] t'` fails
if the conclusion of any theorem `thi` in the list is not an equation; or if
the template `t[x1,...,xn]` does not match the term `t'`; or if and term `ti`
in `t'` marked by the variable `xi` in the template, is not identical to the
left-hand side of the conclusion of the theorem `thi`.

### Example

The values
    
       - val thm0 = SPEC (Term`0`) ADD1
         and thm1 = SPEC (Term`1`) ADD1
         and x = Term`x:num` and y = Term`y:num`;
    
       > val thm0 = |- SUC 0 = 0 + 1 : thm
         val thm1 = |- SUC 1 = 1 + 1 : thm
         val x = `x` : term
         val y = `y` : term
    
can be used to substitute selected occurrences of the terms `SUC 0`
and `SUC 1`
    
    - SUBST_CONV [{redex=x, residue=thm0},{redex=y,residue=thm1}]
                 (Term`(x + y) > SUC 1`)
                 (Term`(SUC 0 + SUC 1) > SUC 1`);
    > val it = |- SUC 0 + SUC 1 > SUC 1 = (0 + 1) + 1 + 1 > SUC 1 : thm
    
The `|->` syntax can also be used:
    
    - SUBST_CONV [x |-> thm0, y |-> thm1]
                 (Term`(x + y) > SUC 1`)
                 (Term`(SUC 0 + SUC 1) > SUC 1`);
    




`SUBST_CONV` is used when substituting at selected occurrences of terms
and using rewriting rules/conversions is too extensive.

### See also

[`Conv.REWR_CONV`](#Conv.REWR_CONV), [`Drule.SUBS`](#Drule.SUBS), [`Thm.SUBST`](#Thm.SUBST), [`Drule.SUBS_OCCS`](#Drule.SUBS_OCCS), [`Lib.|->`](#Lib..GZKQ4)

