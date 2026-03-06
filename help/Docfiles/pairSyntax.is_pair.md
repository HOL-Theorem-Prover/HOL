## `is_pair`

``` hol4
pairSyntax.is_pair : (term -> bool)
```

------------------------------------------------------------------------

Tests a term to see if it is a pair.

`is_pair "(t1,t2)"` returns `true`. If the term is not a pair the result
is `false`.

### Failure

Never fails.

### See also

[`pairSyntax.mk_pair`](#pairSyntax.mk_pair),
[`pairSyntax.dest_pair`](#pairSyntax.dest_pair)
