## `strip_imp_only`

``` hol4
boolSyntax.strip_imp_only : term -> term list * term
```

------------------------------------------------------------------------

Iteratively breaks apart implications.

If `M` is of the form `t1 ==> (... (tn ==> t) ...)`, then
`strip_imp_only M` returns `([t1,...,tn],t)`. Note that

``` hol4
   strip_imp_only(list_mk_imp([t1,...,tn],t))
```

will not return `([t1,...,tn],t)` if `t` is an implication.

### Failure

Never fails.

### Example

``` hol4
- strip_imp_only (Term `(T ==> F) ==> (T ==> F)`);
> val it = ([`T ==> F`, `T`], `F`) : term list * term

- strip_imp_only (Term `t1 ==> t2 ==> t3 ==> ~t`);
> val it = ([`t1`, `t2`, `t3`], `~t`) : term list * term
```

### See also

[`boolSyntax.list_mk_imp`](#boolSyntax.list_mk_imp),
[`boolSyntax.dest_imp`](#boolSyntax.dest_imp)
