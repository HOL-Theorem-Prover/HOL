## `genvar`

``` hol4
Term.genvar : hol_type -> term
```

------------------------------------------------------------------------

Returns a variable whose name has not been used previously.

When given a type, `genvar` returns a variable of that type whose name
has not been used for a variable or constant in the HOL session so far.

### Failure

Never fails.

### Example

The following indicates the typical stylized form of the names (this
should not be relied on, of course):

``` hol4
   - genvar bool;
   > val it = `%%genvar%%1380` : term

   - genvar (Type`:num`);
   > val it = `%%genvar%%1381` : term
```

Note that one can anticipate `genvar`:

``` hol4
   - mk_var("%%genvar%%1382",bool);
   > val it = `%%genvar%%1382` : term

   - genvar bool;
   > val it = `%%genvar%%1382` : term
```

This shortcoming could be guarded against, but it doesn't seem worth it
currently. It doesn't seem to affect the soundness of the implementation
of HOL; at worst, a proof procedure may fail because it doesn't have a
sufficiently fresh variable.

The unique variables are useful in writing derived rules, for
specializing terms without having to worry about such things as free
variable capture. If the names are to be visible to a typical user, the
function `variant` can provide rather more meaningful names.

### See also

[`Drule.GSPEC`](#Drule.GSPEC), [`Term.variant`](#Term.variant)
