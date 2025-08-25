## `inferences`

``` hol4
Count.inferences : ('a -> 'b) -> 'a -> 'b
```

------------------------------------------------------------------------

Counts primitive inferences performed when a function is applied.

The `inferences` function provides a way of counting the primitive
inferences that are performed when a function is applied to its
argument. The reporting of the count is done when the function
terminates (normally, or with an exception).

### Example

``` hol4
- Count.apply (CONJUNCTS o SPEC_ALL) AND_CLAUSES;
Axioms: 0, Defs: 0, Disk: 0, Orcl: 0, Prims: 9; Total: 9
val it =
   [|- T /\ t <=> t, |- t /\ T <=> t,
    |- F /\ t <=> F, |- t /\ F <=> F, |- t /\ t <=> t]: thm list
```

### Failure

The call to `inferences f x` will raise an exception if `f x` would. It
will still report inference counts up to the point of the exception
being raised.

### See also

[`Count.apply`](#Count.apply)
