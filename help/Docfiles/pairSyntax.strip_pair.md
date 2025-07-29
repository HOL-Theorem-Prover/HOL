## `strip_pair`

``` hol4
pairSyntax.strip_pair : term -> term list
```

------------------------------------------------------------------------

Recursively breaks a paired structure into its constituent pieces.

### Example

``` hol4
- strip_pair (Term `((1,2),(3,4))`);
> val it = [`1`, `2`, `3`, `4`] : term list
```

### Comments

Note that `strip_pair` is similar, but not identical, to `spine_pair`
which does not work recursively.

### Failure

Never fails.

### See also

[`pairSyntax.spine_pair`](#pairSyntax.spine_pair)
