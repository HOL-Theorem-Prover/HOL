## `show_numeral_types`

``` hol4
Globals.show_numeral_types : bool ref
```

------------------------------------------------------------------------

A flag which causes numerals to be printed with suffix annotation when
true.

This flag controls the pretty-printing of numeral forms that have been
added to the global grammar with the function `add_numeral_form`. If the
flag is true, then all numeric values are printed with the single-letter
suffixes that identify which type the value is.

### Failure

Never fails, as it is just an SML value.

### Example

``` hol4
- load "integerTheory";
> val it = () : unit

- Term`~3`;
> val it = `~3` : term

- show_numeral_types := true;
> val it = () : unit

- Term`~3`;
> val it = `~3i` : term
```

Can help to disambiguate terms involving numerals.

### See also

[`Parse.add_numeral_form`](#Parse.add_numeral_form),
[`Globals.show_types`](#Globals.show_types)
