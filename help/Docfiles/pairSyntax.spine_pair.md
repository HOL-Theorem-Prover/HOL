## `spine_pair` {#pairSyntax.spine_pair}


```
spine_pair : term -> term list
```



Breaks a paired structure into its constituent pieces.

### Example

    
    - spine_pair (Term `((1,2),(3,4))`);
    > val it = [`(1,2)`, `3`, `4`] : term list
    



### Comments

Note that `spine_pair` is similar, but not identical, to `strip_pair`
which works recursively.

### Failure

Never fails.

### See also

[`pairSyntax.strip_pair`](#pairSyntax.strip_pair)

