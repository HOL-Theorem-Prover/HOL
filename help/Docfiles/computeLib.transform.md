## `transform`

``` hol4
computeLib.type transform
```

------------------------------------------------------------------------

Type of elements in compset

An element of a compset can map to a collection of rewrite rules or a
conversion (or both, in some cases). The type `transform` is declared as
follows:

``` hol4
   datatype transform  
      = Conversion of (term -> thm * db fterm)
      | RRules of thm list
```

### Failure

Can not fail.

### See also

[`computeLib.listItems`](#computeLib.listItems)
