## `apply`

``` hol4
Count.apply : ('a -> 'b) -> 'a -> 'b
```

------------------------------------------------------------------------

Counts primitive inferences performed when a function is applied.

The `apply` function provides a way of counting the primitive inferences
that are performed when a function is applied to its argument. The
reporting of the count is done when the function terminates (normally,
or with an exception). The reporting also includes timing information
about the function call.

### Example

``` hol4
- Count.apply (CONJUNCTS o SPEC_ALL) AND_CLAUSES;
runtime: 0.000s,    gctime: 0.000s,     systime: 0.000s.
Axioms: 0, Defs: 0, Disk: 0, Orcl: 0, Prims: 9; Total: 9
val it =
   [|- T /\ t <=> t,
    |- t /\ T <=> t, |- F /\ t <=> F,
    |- t /\ F <=> F,
    |- t /\ t <=> t]: thm list
```

### Failure

The call to `apply f x` will raise an exception if `f x` would. It will
still report elapsed time and inference counts up to the point of the
exception being raised.

### See also

[`Count.thm_count`](#Count.thm_count)
