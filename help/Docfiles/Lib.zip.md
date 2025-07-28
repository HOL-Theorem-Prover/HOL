## `zip` {#Lib.zip}


```
zip : 'a list -> 'b list -> ('a * 'b) list
```



Transforms a pair of lists into a list of pairs.


`zip [x1,...,xn] [y1,...,yn]` returns `[(x1,y1),...,(xn,yn)]`.

### Failure

Fails if the two lists are of different lengths.

### Comments

Has much the same effect as the SML Basis function `ListPair.zip` except
that it fails if the arguments are not of equal length. `zip` is a
curried version of `combine`

### See also

[`Lib.combine`](#Lib.combine), [`Lib.unzip`](#Lib.unzip), [`Lib.split`](#Lib.split)

