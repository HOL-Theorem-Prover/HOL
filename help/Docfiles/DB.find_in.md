## `find_in`

``` hol4
DB.find_in : string -> data list -> data list
```

------------------------------------------------------------------------

Search for theory element by name fragment, among a given list.

An invocation `DB.find_in s data_list` selects from `data_list` those
theory elements which have been stored with a name in which `s` occurs
as a proper substring, ignoring case distinctions.

### Failure

Never fails. If nothing suitable can be found, the empty list is
returned.

### Example

``` hol4
- DB.find "inc";
> val it =
    [(("arithmetic", "MULT_INCREASES"),
      (|- !m n. 1 < m /\ 0 < n ==> SUC n <= m * n, Thm)),
     (("bool", "BOOL_EQ_DISTINCT"), (|- ~(T = F) /\ ~(F = T), Thm)),
     (("list", "list_distinct"), (|- !a1 a0. ~([] = a0::a1), Thm)),
     (("sum", "sum_distinct"), (|- !x y. ~(INL x = INR y), Thm)),
     (("sum", "sum_distinct1"), (|- !x y. ~(INR y = INL x), Thm))]
  : ((string * string) * (thm * class)) list

- DB.find_in "sum" it;
> val it =
    [(("sum", "sum_distinct"), (|- !x y. ~(INL x = INR y), Thm)),
     (("sum", "sum_distinct1"), (|- !x y. ~(INR y = INL x), Thm))]
  : ((string * string) * (thm * class)) list
```

Finding theorems in interactive proof sessions. The second argument will
normally be the result of a previous call to
`DB.find, DB.match, DB.apropos, DB.listDB, DB.thy` etc.

### See also

[`DB.find`](#DB.find), [`DB.match`](#DB.match),
[`DB.apropos`](#DB.apropos), [`DB.listDB`](#DB.listDB),
[`DB.thy`](#DB.thy), [`DB.theorems`](#DB.theorems)
