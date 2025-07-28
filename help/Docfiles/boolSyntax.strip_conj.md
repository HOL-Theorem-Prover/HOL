## `strip_conj` {#boolSyntax.strip_conj}


```
strip_conj : term -> term list
```



Recursively breaks apart conjunctions.


If `M` is of the form `t1 /\ ... /\ tn`, where no `ti` is a conjunction,
then `strip_conj M` returns `[t1,...,tn]`. Any `ti` that is a conjunction
is broken down by `strip_conj`, hence
    
       strip_conj(list_mk_conj [t1,...,tn])
    
will not return `[t1,...,tn]` if any `ti` is a conjunction.

### Failure

Never fails.

### Example

    
    - strip_conj (Term `(a /\ b) /\ c /\ d`);
    > val it = [`a`, `b`, `c`, `d`] : term list
    



### See also

[`boolSyntax.dest_conj`](#boolSyntax.dest_conj), [`boolSyntax.mk_conj`](#boolSyntax.mk_conj), [`boolSyntax.list_mk_conj`](#boolSyntax.list_mk_conj)

