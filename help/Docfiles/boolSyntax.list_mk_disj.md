## `list_mk_disj`

``` hol4
boolSyntax.list_mk_disj : term list -> term
```

------------------------------------------------------------------------

Constructs the disjunction of a list of terms.

`list_mk_disj([t1,...,tn])` returns `t1 \/ ... \/ tn`.

### Failure

Fails if the list is empty or if the list has more than one element, one
or more of which are not of type `bool`.

### Example

``` hol4
- list_mk_disj [T,F,T];
> val it = `T \/ F \/ T` : term

- try list_mk_disj [T,mk_var("x",alpha),F];

Exception raised at boolSyntax.mk_disj:
Non-boolean argument

- list_mk_disj [mk_var("x",alpha)];
> val it = `x` : term
```

### See also

[`boolSyntax.strip_disj`](#boolSyntax.strip_disj),
[`boolSyntax.mk_disj`](#boolSyntax.mk_disj)
