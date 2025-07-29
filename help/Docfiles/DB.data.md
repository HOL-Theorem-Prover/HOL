## `data`

``` hol4
DB.type data
```

------------------------------------------------------------------------

Type abbreviation used in `DB` structure.

When functions from the `DB` structure are used to query the current
theory, answer are often phrased in terms of the `data` type, which is a
type abbreviation declared as

``` hol4
   type data = (string * string) * (thm * class)
```

An element `((thy,name), (th,cl))` means that `th` is a theorem with
classification `class`, stored in theory segment `thy` under `name`.

### Example

``` hol4
- DB.find "BOOL_CASES_AX";
> val it = [(("bool", "BOOL_CASES_AX"),
            (|- !t. (t = T) \/ (t = F), Axm))]
   : ((string * string) * (thm * class)) list
```

### See also

[`DB.class`](#DB.class), [`DB.thy`](#DB.thy), [`DB.find`](#DB.find),
[`DB.match`](#DB.match), [`DB.apropos`](#DB.apropos),
[`DB.listDB`](#DB.listDB)
