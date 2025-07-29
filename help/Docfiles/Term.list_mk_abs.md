## `list_mk_abs`

``` hol4
Term.list_mk_abs : term list * term -> term
```

------------------------------------------------------------------------

Performs a sequence of lambda binding operations.

An application `list_mk_abs ([v1,...,vn], M)` yields the term
`\v1 ... vn. M`. Free occurrences of `v1,...,vn` in `M` become bound in
the result.

### Failure

Fails if some `vi` (1 \<= i \<= n) is not a variable.

### Example

``` hol4
- list_mk_abs ([mk_var("v1",bool),mk_var("v2",bool),mk_var("v3",bool)],
               Term `v1 /\ v2 /\ v3`);
> val it = `\v1 v2 v3. v1 /\ v2 /\ v3` : term
```

### Comments

In the current implementation, `list_mk_abs` is more efficient than
iteration of `mk_abs` for larger tasks.

### See also

[`Term.mk_abs`](#Term.mk_abs),
[`boolSyntax.list_mk_forall`](#boolSyntax.list_mk_forall),
[`boolSyntax.list_mk_exists`](#boolSyntax.list_mk_exists)
