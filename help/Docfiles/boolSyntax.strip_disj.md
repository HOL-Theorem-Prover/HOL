## `strip_disj` {#boolSyntax.strip_disj}


```
strip_disj : term -> term list
```



Recursively breaks apart disjunctions.


If `M` is of the form `t1 \/ ... \/ tn`, where no `ti` is a disjunction,
then `strip_disj M` returns `[t1,...,tn]`. Any `ti` that is a disjunction
is broken down by `strip_disj`, hence
    
       strip_disj(list_mk_disj [t1,...,tn])
    
will not return `[t1,...,tn]` if any `ti` is a disjunction.

### Failure

Never fails.

### Example

    
    - strip_disj (Term `(a \/ b) \/ c \/ d`);
    > val it = [`a`, `b`, `c`, `d`] : term list
    



### See also

[`boolSyntax.dest_disj`](#boolSyntax.dest_disj), [`boolSyntax.mk_disj`](#boolSyntax.mk_disj), [`boolSyntax.list_mk_disj`](#boolSyntax.list_mk_disj)

