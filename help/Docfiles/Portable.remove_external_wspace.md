## `remove_external_wspace`

``` hol4
Portable.remove_external_wspace : string -> string
```

------------------------------------------------------------------------

Removes trailing and leading whitespace characters from a string

A call to `remove_external_wspace s` returns a string identical to `s`
except that all leading and trailing characters for which `Char.isSpace`
is true have been removed. The implementation is (with the Basis's
`Substring` structure open):

``` hol4
   string (dropl Char.isSpace (dropr Char.isSpace (full s)))
```

### Failure

Never fails.

### See also

[`Portable.remove_wspace`](#Portable.remove_wspace)
