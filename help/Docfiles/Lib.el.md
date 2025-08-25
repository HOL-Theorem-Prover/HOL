## `el`

``` hol4
Lib.el : int -> 'a list -> 'a
```

------------------------------------------------------------------------

Extracts a specified element from a list.

`el i [x1,...,xn]` returns `xi`. Note that the elements are numbered
starting from `1`, not `0`.

### Failure

Fails with `el` if the integer argument is less than 1 or greater than
the length of the list.

### Example

``` hol4
- el 3 [1,2,7,1];
> val it = 7 : int
```

### See also

[`Lib.index`](#Lib.index)
