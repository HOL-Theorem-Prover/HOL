## `mapfilter`

``` hol4
Lib.mapfilter : ('a -> 'b) -> 'a list -> 'b list
```

------------------------------------------------------------------------

Like map, but drops elements that raise exceptions.

Applies a function to every element of a list, returning a list of
results for those elements for which application succeeds. The function
is applied to the elements of the list from left to right (which is
significant if its action includes side effects).

### Failure

If `f x` raises `Interrupt` for some element `x` of `l`, then
`mapfilter f l` fails (with an `Interrupt` exception).

### Example

``` hol4
- mapfilter hd [[1,2,3],[4,5],[],[6,7,8],[]];
> val it = [1, 4, 6] : int list
```

### See also

[`Lib.filter`](#Lib.filter)
