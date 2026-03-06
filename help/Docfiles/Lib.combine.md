## `combine`

``` hol4
Lib.combine : 'a list * 'b list -> ('a * 'b) list
```

------------------------------------------------------------------------

Transforms a pair of lists into a list of pairs.

`combine ([x1,...,xn],[y1,...,yn])` returns `[(x1,y1),...,(xn,yn)]`.

### Failure

Fails if the two lists are of different lengths.

### Comments

Has much the same effect as the SML Basis function `ListPair.zip` except
that it fails if the arguments are not of equal length. Also note that
`zip` is a curried version of `combine`

### See also

[`Lib.zip`](#Lib.zip), [`Lib.unzip`](#Lib.unzip),
[`Lib.split`](#Lib.split)
