## `strip_comb`

``` hol4
boolSyntax.strip_comb : term -> term * term list
```

------------------------------------------------------------------------

Iteratively breaks apart combinations (function applications).

If `M` has the form `t t1 ... tn` then `strip_comb M` returns
`(t,[t1,...,tn])`. Note that

``` hol4
   strip_comb(list_mk_comb(t,[t1,...,tn]))
```

will not be `(t,[t1,...,tn])` if `t` is a combination.

### Failure

Never fails.

### Example

``` hol4
- strip_comb (Term `x /\ y`);
> val it = (`$/\`, [`x`, `y`]) : term * term list

- strip_comb T;
> val it = (`T`, []) : term * term list
```

### See also

[`Term.list_mk_comb`](#Term.list_mk_comb),
[`Term.dest_comb`](#Term.dest_comb)
