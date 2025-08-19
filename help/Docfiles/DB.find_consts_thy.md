## `find_consts_thy`

``` hol4
DB.find_consts_thy : string list -> hol_type -> term list
```

------------------------------------------------------------------------

Searches in the theories in list `thl` for a constant matching given
type `ty`.

A call to `find_consts_thy thl ty` searches the theories with names from
`thl` for constants whose types match type `ty`, and returns that list.

### Failure

Never fails.

### Example

If we run

``` hol4
   > find_consts_thy ["bool"] ``:'a -> 'a set -> bool``;
   val it = [“$IN”]: term list
```

and

``` hol4
   > find_consts_thy ["arithmetic"] ``:num -> num -> num``;
   val it = [“$*”, “$+”, “$-”, “ABS_DIFF”, “$DIV”, “$**”, “MAX”, “MIN”,
             “$MOD”]: term list
```

### See also

[`bossLib.find_consts`](#bossLib.find_consts),
[`DB.apropos`](#DB.apropos), [`DB.find`](#DB.find)
