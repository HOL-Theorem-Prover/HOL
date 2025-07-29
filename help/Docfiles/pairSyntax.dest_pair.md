## `dest_pair`

``` hol4
pairSyntax.dest_pair : term -> term * term
```

------------------------------------------------------------------------

Breaks apart a pair into two separate terms.

`dest_pair` is a term destructor for pairs: if `M` is a term of the form
`(t1,t2)`, then `dest_pair M` returns `(t1,t2)`.

### Failure

Fails if `M` is not a pair.

### See also

[`pairSyntax.mk_pair`](#pairSyntax.mk_pair),
[`pairSyntax.is_pair`](#pairSyntax.is_pair),
[`pairSyntax.strip_pair`](#pairSyntax.strip_pair)
