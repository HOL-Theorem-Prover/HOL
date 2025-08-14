## `list_mk_pair`

``` hol4
pairSyntax.list_mk_pair : term list -> term
```

------------------------------------------------------------------------

Constructs a tuple from a list of terms.

`list_mk_pair([t1,...,tn])` returns the term `(t1,...,tn)`.

### Failure

Fails if the list is empty.

### Example

``` hol4
- pairSyntax.list_mk_pair [Term `1`, T, Term `2`];
> val it = `(1,T,2)` : term

- pairSyntax.list_mk_pair [Term `1`];
> val it = `1` : term
```

### See also

[`pairSyntax.strip_pair`](#pairSyntax.strip_pair),
[`pairSyntax.mk_pair`](#pairSyntax.mk_pair)
