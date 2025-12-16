## `axioms`

``` hol4
DB.axioms : string -> (string * thm) list
```

------------------------------------------------------------------------

All the axioms stored in the named theory.

An invocation `axioms thy`, where `thy` is the name of a currently
loaded theory segment, will return a list of the axioms stored in that
theory. Each theorem is paired with its name in the result. The string
`"-"` may be used to denote the current theory segment.

### Failure

Never fails. If `thy` is not the name of a currently loaded theory
segment, the empty list is returned.

### Example

``` hol4
- axioms "bool";
> val it =
    [("INFINITY_AX", |- ?f. ONE_ONE f /\ ~ONTO f),
     ("SELECT_AX", |- !P x. P x ==> P ($@ P)),
     ("ETA_AX", |- !t. (\x. t x) = t),
     ("BOOL_CASES_AX", |- !t. (t = T) \/ (t = F))] : (string * thm) list
```

### See also

[`DB.thy`](#DB.thy), [`DB.fetch`](#DB.fetch), [`DB.thms`](#DB.thms),
[`DB.theorems`](#DB.theorems), [`DB.definitions`](#DB.definitions),
[`DB.listDB`](#DB.listDB)
