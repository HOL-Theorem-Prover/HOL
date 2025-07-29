## `unzip`

``` hol4
Lib.unzip : ('a * 'b) list -> ('a list * 'b list)
```

------------------------------------------------------------------------

Converts a list of pairs into a pair of lists.

`unzip [(x1,y1),...,(xn,yn)]` returns `([x1,...,xn],[y1,...,yn])`.

### Failure

Never fails.

### Comments

Identical to `Lib.split`.

### See also

[`Lib.split`](#Lib.split), [`Lib.zip`](#Lib.zip),
[`Lib.combine`](#Lib.combine)
