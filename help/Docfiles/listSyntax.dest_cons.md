## `dest_cons`

``` hol4
listSyntax.dest_cons : term -> term * term
```

------------------------------------------------------------------------

Breaks apart a 'CONS pair' into head and tail.

`dest_cons` is a term destructor for 'CONS pairs'. When applied to a
term representing a nonempty list `[t;t1;...;tn]` (which is equivalent
to `CONS t [t1;...;tn]`), it returns the pair of terms
`(t, [t1;...;tn])`.

### Failure

Fails if the term is an empty list.

### See also

[`listSyntax.mk_cons`](#listSyntax.mk_cons),
[`listSyntax.is_cons`](#listSyntax.is_cons),
[`listSyntax.mk_list`](#listSyntax.mk_list),
[`listSyntax.dest_list`](#listSyntax.dest_list),
[`listSyntax.is_list`](#listSyntax.is_list)
