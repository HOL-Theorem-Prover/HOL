## `is_cons`

``` hol4
listSyntax.is_cons : (term -> bool)
```

------------------------------------------------------------------------

Tests a term to see if it is an application of `CONS`.

`is_cons` returns `true` of a term representing a non-empty list.
Otherwise it returns `false`.

### Failure

Never fails.

### See also

[`listSyntax.mk_cons`](#listSyntax.mk_cons),
[`listSyntax.dest_cons`](#listSyntax.dest_cons),
[`listSyntax.mk_list`](#listSyntax.mk_list),
[`listSyntax.dest_list`](#listSyntax.dest_list),
[`listSyntax.is_list`](#listSyntax.is_list)
