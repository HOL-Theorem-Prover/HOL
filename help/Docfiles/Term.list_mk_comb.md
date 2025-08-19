## `list_mk_comb`

``` hol4
Term.list_mk_comb : term * term list -> term
```

------------------------------------------------------------------------

Iteratively constructs combinations (function applications).

`list_mk_comb(t,[t1,...,tn])` returns `t t1 ... tn`.

### Failure

Fails if the types of `t1`,...,`tn` are not equal to the argument types
of `t`. It is not necessary for all the arguments of `t` to be given. In
particular the list of terms `t1`,...,`tn` may be empty.

### Example

``` hol4
- list_mk_comb(conditional,[T, mk_var("one",alpha), mk_var("two",alpha)]);
> val it = `(if T then one else two)` : term

- list_mk_comb(universal,[]);
> val it = `$!` : term

- try list_mk_comb(universal,[F]);

Exception raised at Term.list_mk_comb:
incompatible types
```

### See also

[`boolSyntax.strip_comb`](#boolSyntax.strip_comb),
[`Term.mk_comb`](#Term.mk_comb)
