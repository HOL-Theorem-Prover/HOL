## `split`

``` hol4
Lib.split : ('a * 'b) list -> ('a list * 'b list)
```

------------------------------------------------------------------------

Converts a list of pairs into a pair of lists.

`split [(x1,y1),...,(xn,yn)]` returns `([x1,...,xn],[y1,...,yn])`.

### Failure

Never fails.

### Comments

Identical to the Basis function `ListPair.unzip` and the function
`Lib.unzip`.

### See also

[`Lib.unzip`](#Lib.unzip), [`Lib.zip`](#Lib.zip),
[`Lib.combine`](#Lib.combine)
