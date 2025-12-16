## `ppstring`

``` hol4
Lib.ppstring : 'a PP.pprinter -> 'a -> string
```

------------------------------------------------------------------------

Pretty-prints a value into a string.

A call to `ppstring ppf x` will call the pretty-printing function `ppf`
on value `x`, with the pretty-printing output stored in the string that
is eventually returned to the user. The linewidth used for determining
when to wrap with newline characters is given by the reference
`Globals.linewidth` (typically 72).

### Failure

Fails if the pretty-printing function fails on the particular input
value.

### Example

``` hol4
> ppstring PP.add_string "hello"
val it = "hello": string
```

### Comments

The returned string may contain unwanted terminal-specific escape codes,
see `rawterm_pp`.

### See also

[`Portable.pprint`](#Portable.pprint),
[`Parse.term_to_string`](#Parse.term_to_string),
[`Parse.rawterm_pp`](#Parse.rawterm_pp)
