## `clear_overloads_on`

``` hol4
Parse.clear_overloads_on : string -> unit
```

------------------------------------------------------------------------

Clears all overloading on the specified operator.

This function removes all overloading associated with the given string,
except those "overloads" that map the string to constants of the same
name. These additional overloads (there may be more than one constant of
the same name, as long as each such is part of a different theory) may
be removed with `remove_ovl_mapping`, or by using `hide`.

### Failure

Never fails. If a string is not overloaded, this function simply has no
effect.

### Example

``` hol4
- load "realTheory";
> val it = () : unit
- realTheory.REAL_INV_LT1;
> val it = |- !x. 0 < x /\ x < 1 ==> 1 < inv x : thm
- clear_overloads_on "<";
> val it = () : unit
- realTheory.REAL_INV_LT1;
> val it = |- !x. 0 real_lt x /\ x real_lt 1 ==> 1 real_lt inv x : thm
- clear_overloads_on "&";
> val it = () : unit
- realTheory.REAL_INV_LT1;
> val it = |- !x. 0r real_lt x /\ x real_lt 1r ==> 1r real_lt inv x : thm
```

If overloading gets too confusing, this function should help to clear
away one layer of supposedly helpful obfuscation.

### Comments

As with other parsing functions, there is a sister function,
`temp_clear_overloads_on` that does the same thing, but whose effect is
not saved to a theory file.

### See also

[`Parse.overload_on`](#Parse.overload_on),
[`Parse.remove_ovl_mapping`](#Parse.remove_ovl_mapping)
