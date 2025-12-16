## `prefer_int`

``` hol4
intLib.prefer_int : unit -> unit
```

------------------------------------------------------------------------

Makes the parser favour integer possibilities in ambiguous terms.

Calling `prefer_int()` causes the global grammar to be altered so that
the standard arithmetic operator symbols (`+`, `*`, etc.), as well as
numerals, are given integral types if possible. This effect is brought
about through the application of multiple calls to `temp_overload_on`,
so that the "arithmetic symbols" need not have been previously mapping
to integral possibilities at all (as would be the situation after a call
to `deprecate_int`).

### Failure

Never fails.

### See also

[`intLib.deprecate_int`](#intLib.deprecate_int),
[`Parse.overload_on`](#Parse.overload_on)
