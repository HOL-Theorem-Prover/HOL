## `mk_pair`

``` hol4
pairSyntax.mk_pair : term * term -> term
```

------------------------------------------------------------------------

Constructs object-level pair from a pair of terms.

`mk_pair (t1,t2)` returns `(t1,t2)`.

### Failure

Never fails.

### See also

[`pairSyntax.dest_pair`](#pairSyntax.dest_pair),
[`pairSyntax.is_pair`](#pairSyntax.is_pair),
[`pairSyntax.list_mk_pair`](#pairSyntax.list_mk_pair)
