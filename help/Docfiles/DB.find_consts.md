## `find_consts`

``` hol4
DB.find_consts : hol_type -> term list
```

------------------------------------------------------------------------

Searches the current theory and its ancestors for constants matching
given type.

Given a type `ty` searches the current theory and its ancestors for
constants whose type matches the ("pattern") type `ty`.

### Failure

Never fails.

### Example

If we run

``` hol4
   > find_consts ``:'a -> 'a set -> bool``;
   val it = [“$IN”]: term list
```

and with

``` hol4
   > find_consts ``:num -> num -> num``;
   val it =
      [“napp”, “ncons”, “$*,”, “internal_mult”, “numeral$onecount”,
       “numeral$texp_help”, “$*”, “$+”, “$-”, “ABS_DIFF”, “$DIV”,
       “$**”, “MAX”, “MIN”, “$MOD”, “ind_type$NUMPAIR”]: term list
```

The fact that type-matching is performed is apparent with this call:

``` hol4
   > find_consts ``:'a -> 'a``;
   val it =
      [“TL_T”, “common_prefixes”, “FRONT”, “REVERSE”, “TL”, “nub”,
       “COMPL”, “REST”, “tri⁻¹”, “nfst”, “nlen”, “nmap”, “nsnd”,
       “tri”, “numeral$exactlog”, “numeral$iDUB”, “numeral$iSQR”,
       “numeral$iZ”, “numeral$iiSUC”, “BIT1”, “BIT2”, “DIV2”, “FACT”,
       “NUMERAL”, “$&”, “PRE”, “SUC”, “SUC_REP”, “Abbrev”, “Cong”,
       “stmarker”, “unint”, “BOUNDED”, “LET”, “literal_case”, “$~”,
       “EQC”, “RC”, “RCOMPL”, “RTC”, “SC”, “STRORD”, “TC”, “I”,
       “NUMFST”, “NUMRIGHT”, “NUMSND”]: term list
```

where both `SUC` and `$~` (boolean negation) are among the list
returned.

### See also

[`bossLib.find_consts_thy`](#bossLib.find_consts_thy),
[`DB.apropos`](#DB.apropos), [`DB.find`](#DB.find)
