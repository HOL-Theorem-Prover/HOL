## `ADD_ASSUM`

``` hol4
Drule.ADD_ASSUM : term -> thm -> thm
```

------------------------------------------------------------------------

Adds an assumption to a theorem.

When applied to a boolean term `s` and a theorem `A |- t`, the inference
rule `ADD_ASSUM` returns the theorem `A u {s} |- t`.

``` hol4
       A |- t
   --------------  ADD_ASSUM s
    A u {s} |- t
```

### Failure

Fails unless the given term has type `bool`.

### See also

[`Thm.ASSUME`](#Thm.ASSUME), [`Drule.UNDISCH`](#Drule.UNDISCH)
