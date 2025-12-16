## `listDB`

``` hol4
DB.listDB : unit -> data list
```

------------------------------------------------------------------------

All theorems, axioms, and definitions in the currently loaded theory
segments.

An invocation `listDB()` returns everything that has been stored in all
theory segments currently loaded.

### Example

``` hol4
- length (listDB());
> val it = 736 : int
```

### See also

[`DB.thy`](#DB.thy), [`DB.theorems`](#DB.theorems),
[`DB.definitions`](#DB.definitions), [`DB.axioms`](#DB.axioms),
[`DB.find`](#DB.find), [`DB.match`](#DB.match)
