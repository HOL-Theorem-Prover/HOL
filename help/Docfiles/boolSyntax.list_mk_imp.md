## `list_mk_imp`

``` hol4
boolSyntax.list_mk_imp : term list * term -> term
```

------------------------------------------------------------------------

Iteratively constructs implications.

`list_mk_imp([t1,...,tn],t)` returns `t1 ==> ( ... (tn ==> t)...)`.

### Failure

Fails if any of `t1`,...,`tn` are not of type `bool`. Also fails if the
list of terms is non-empty and `t` is not of type `bool`. If the list of
terms is empty the type of `t` can be anything.

### Example

``` hol4
- list_mk_imp ([T,F],T);
> val it = `T ==> F ==> T` : term


- try list_mk_imp ([T,F],mk_var("x",alpha));
evaluation failed     list_mk_imp

- list_mk_imp ([],mk_var("x",alpha));
> val it = `x` : term
```

### See also

[`boolSyntax.strip_imp`](#boolSyntax.strip_imp),
[`boolSyntax.mk_imp`](#boolSyntax.mk_imp)
