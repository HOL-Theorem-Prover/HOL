## `empty_varset`

``` hol4
Term.empty_varset : term set
```

------------------------------------------------------------------------

Empty set of term variables.

The value `empty_varset` represents an empty set of term variables. The
set has a built-in ordering, which is given by `Term.var_compare`.

### Comments

Used as a starting point for building sets of variables.

### See also

[`Term.var_compare`](#Term.var_compare),
[`Term.empty_tmset`](#Term.empty_tmset)
