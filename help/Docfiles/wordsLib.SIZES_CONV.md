## `SIZES_CONV`

``` hol4
wordsLib.SIZES_CONV : conv
```

------------------------------------------------------------------------

Evaluates `dimindex`, `dimword` and `INT_MIN`.

### Example

``` hol4
- SIZES_CONV “dimword(:32)”
> val it = |- dimword (:32) = 4294967296 : thm
```

### Comments

Evaluations are stored and so will be slightly faster when repeated.

### See also

[`wordsLib.SIZES_ss`](#wordsLib.SIZES_ss)
