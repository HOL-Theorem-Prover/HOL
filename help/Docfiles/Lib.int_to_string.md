## `int_to_string`

``` hol4
Lib.int_to_string : int -> string
```

------------------------------------------------------------------------

Translates an integer into a string.

An application `int_to_string i` returns the printable form of `i`.

### Failure

Never fails.

### Example

``` hol4
- int_to_string 12323;
> val it = "12323" : string

- int_to_string ~1;
> val it = "~1" : string
```

### Comments

Equivalent functionality can be found in the Standard ML Basis Library
function `Int.toString`.

### See also

[`Lib.string_to_int`](#Lib.string_to_int)
