## `genvarstruct`

``` hol4
pairSyntax.genvarstruct : hol_type -> term
```

------------------------------------------------------------------------

Returns a pair structure of variables whose names have not been
previously used.

When given a product type, `genvarstruct` returns a paired structure of
variables whose names have not been used for variables or constants in
the HOL session so far. The structure of the term returned will be
identical to the structure of the argument.

### Failure

Never fails.

### Example

The following example illustrates the behaviour of `genvarstruct`:

``` hol4
   - genvarstruct (type_of (Term `((1,2),(x:'a,x:'a))`));
   > val it = `((%%genvar%%1535,%%genvar%%1536),%%genvar%%1537,%%genvar%%1538)`
      : term
```

Unique variables are useful in writing derived rules, for specializing
terms without having to worry about such things as free variable
capture. It is often important in such rules to keep the same structure.
If not, `genvar` will be adequate. If the names are to be visible to a
typical user, the function `pvariant` can provide rather more meaningful
names.

### See also

[`Term.genvar`](#Term.genvar), [`PairRules.GPSPEC`](#PairRules.GPSPEC),
[`pairSyntax.pvariant`](#pairSyntax.pvariant)
