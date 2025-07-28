## `P_PSKOLEM_CONV` {#PairRules.P_PSKOLEM_CONV}


```
P_PSKOLEM_CONV : (term -> conv)
```



Introduces a user-supplied Skolem function.


`P_PSKOLEM_CONV` takes two arguments.  The first is a variable `f`, which
must range over functions of the appropriate type, and the second is a term of
the form `!p1...pn. ?q. t` (where `pi` and `q` may be pairs).
Given these arguments, `P_PSKOLEM_CONV` returns the theorem:
    
       |- (!p1...pn. ?q. t) = (?f. !p1...pn. tm[f p1 ... pn/q])
    
which expresses the fact that a skolem function `f` of the
universally quantified variables `p1...pn` may be introduced in place of the
the existentially quantified pair `p`.

### Failure

`P_PSKOLEM_CONV f tm` fails if `f` is not a variable, or if the input term `tm`
is not a term of the form `!p1...pn. ?q. t`, or if the variable `f` is free in
`tm`, or if the type of `f` does not match its intended use as an `n`-place
curried function from the pairs `p1...pn` to a value having the same type
as `p`.

### See also

[`Conv.X_SKOLEM_CONV`](#Conv.X_SKOLEM_CONV), [`PairRules.PSKOLEM_CONV`](#PairRules.PSKOLEM_CONV)

