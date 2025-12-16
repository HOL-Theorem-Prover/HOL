## `pprint`

``` hol4
Portable.pprint : ‘a PP.pprinter -> 'a -> unit
```

------------------------------------------------------------------------

Pretty-prints a value to output

A call to `pprint ppf x` will call the pretty-printing function `ppf` on
value `x`, with the pretty-printing output printed. string that is
eventually returned to the user. The linewidth used for determining when
to wrap with newline characters is 72.

### Failure

Fails if the pretty-printing function fails on the particular input
value.

### Example

``` hol4
> pprint PP.add_string "hello";
hello
val it = (): unit
```

### See also

[`Lib.ppstring`](#Lib.ppstring)
