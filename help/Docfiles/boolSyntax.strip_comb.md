## `strip_comb` {#boolSyntax.strip_comb}


```
strip_comb : term -> term * term list
```



Iteratively breaks apart combinations (function applications).


If `M` has the form `t t1 ... tn` then `strip_comb M` returns
`(t,[t1,...,tn])`. Note that
    
       strip_comb(list_mk_comb(t,[t1,...,tn]))
    
will not be `(t,[t1,...,tn])` if `t` is a combination.

### Failure

Never fails.

### Example

    
    - strip_comb (Term `x /\ y`);
    > val it = (`$/\`, [`x`, `y`]) : term * term list
    
    - strip_comb T;
    > val it = (`T`, []) : term * term list
    



### See also

[`Term.list_mk_comb`](#Term.list_mk_comb), [`Term.dest_comb`](#Term.dest_comb)

