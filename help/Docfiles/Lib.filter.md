## `filter` {#Lib.filter}


```
filter : ('a -> bool) -> 'a list -> 'a list
```



Filters a list to the sublist of elements satisfying a predicate.


`filter P l` applies `P` to every element of `l`, returning a list of those
that satisfy `P`, in the order they appeared in the original list.

### Failure

If `P x` fails for some element `x` of `l`.

### Comments

Identical to `List.filter` from the Standard ML Basis Library.

### See also

[`Lib.mapfilter`](#Lib.mapfilter), [`Lib.partition`](#Lib.partition)

