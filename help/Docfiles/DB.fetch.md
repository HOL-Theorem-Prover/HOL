## `fetch`

``` hol4
DB.fetch : string -> string -> thm
```

------------------------------------------------------------------------

Fetch a theorem by theory and name.

An invocation `fetch thy name` searches through the currently loaded
theory segments in an attempt to find a theorem, axiom, or definition
stored under `name` in theory `thy`.

### Failure

If the specified theorem, axiom, or definition cannot be located.

### Example

``` hol4
- DB.fetch "bool" "NOT_FORALL_THM";
> val it = |- !P. ~(!x. P x) = ?x. ~P x : thm
```

### See also

[`DB.thms`](#DB.thms), [`DB.thy`](#DB.thy),
[`DB.theorems`](#DB.theorems), [`DB.axioms`](#DB.axioms),
[`DB.definitions`](#DB.definitions)
