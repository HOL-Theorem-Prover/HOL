## `mk_pabs`

``` hol4
pairSyntax.mk_pabs : term * term -> term
```

------------------------------------------------------------------------

Constructs a paired abstraction.

If `M` is the tuple `(v1,..(..)..,vn)`, and `N` is an arbitrary term,
then `mk_pabs (M,N)` returns the paired abstraction
`` `\(v1,..(..)..,vn).N` ``.

### Failure

Fails unless `M` is an arbitrarily nested pair composed from variables,
with no repetitions of variables.

### See also

[`pairSyntax.dest_pabs`](#pairSyntax.dest_pabs),
[`pairSyntax.is_pabs`](#pairSyntax.is_pabs),
[`Term.mk_abs`](#Term.mk_abs)
