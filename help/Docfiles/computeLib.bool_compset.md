## `bool_compset`

``` hol4
computeLib.bool_compset : unit -> compset
```

------------------------------------------------------------------------

Creates a new simplification set to use with `CBV_CONV` for basic
computations.

This function creates a new simplification set to use with the compute
library performing computations about operations on primitive booleans
and other basic constants, such as LET, conditional, implication,
conjunction, disjunction, and negation.

### Example

``` hol4
- CBV_CONV (bool_compset()) (Term `F ==> (T \/ F)`);
> val it = |- F ==> (T \/ F) = T : thm
```

### See also

[`computeLib.CBV_CONV`](#computeLib.CBV_CONV)
