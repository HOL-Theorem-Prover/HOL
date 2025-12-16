## `var_compare`

``` hol4
Term.var_compare : term * term -> order
```

------------------------------------------------------------------------

Total ordering on variables.

An invocation `var_compare (v1,v2)` will return one of
`{LESS, EQUAL, GREATER}`, according to an ordering on term variables.
The ordering is transitive and total.

### Failure

If `v1` and `v2` are not both variables.

### Example

``` hol4
- var_compare (mk_var("x",bool), mk_var("x",bool --> bool));
> val it = LESS : order
```

### Comments

Used to build high performance datastructures for dealing with sets
having many variables.

### See also

[`Term.empty_varset`](#Term.empty_varset),
[`Term.compare`](#Term.compare)
