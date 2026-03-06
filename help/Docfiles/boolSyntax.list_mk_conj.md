## `list_mk_conj`

``` hol4
boolSyntax.list_mk_conj : term list -> term
```

------------------------------------------------------------------------

Constructs the conjunction of a list of terms.

`list_mk_conj([t1,...,tn])` returns `t1 /\ ... /\ tn`.

### Failure

Fails if the list is empty or if the list has more than one element, one
or more of which are not of type `bool`.

### Example

``` hol4
- list_mk_conj [T,F,T];
> val it = `T /\ F /\ T` : term

- try list_mk_conj [T,mk_var("x",alpha),F];

Exception raised at boolSyntax.mk_conj:
Non-boolean argument

- list_mk_conj [mk_var("x",alpha)];
> val it = `x` : term
```

### See also

[`boolSyntax.strip_conj`](#boolSyntax.strip_conj),
[`boolSyntax.mk_conj`](#boolSyntax.mk_conj)
