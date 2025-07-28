## `strip_imp` {#boolSyntax.strip_imp}


```
strip_imp : term -> term list * term
```



Iteratively breaks apart implications.


If `M` is of the form `t1 ==> (... (tn ==> t) ...)`, then `strip_imp M`
returns `([t1,...,tn],t)`. Note that
    
       strip_imp(list_mk_imp([t1,...,tn],t))
    
will not return `([t1,...,tn],t)` if `t` is an implication.

### Failure

Never fails.

### Example

    
    - strip_imp "(T ==> F) ==> (T ==> F)";;
    > val it = (["T ==> F"; "T"], "F") : term list * term
    
    - strip_imp (Term `t1 ==> t2 ==> t3 ==> ~t`);
    > val it = ([`t1`, `t2`, `t3`, `t`], `F`) : term list * term
    



### See also

[`boolSyntax.list_mk_imp`](#boolSyntax.list_mk_imp), [`boolSyntax.dest_imp`](#boolSyntax.dest_imp)

