## `front_last`

``` hol4
Lib.front_last : 'a list -> 'a list * 'a
```

------------------------------------------------------------------------

Takes a non-empty list `L` and returns a pair `(front,last)` such that
`front @ [last] = L`.

### Failure

Fails if the list is empty.

### Example

``` hol4
- front_last [1];
> val it = ([],1) : int list * int

- front_last [1,2,3];
> val it = ([1,2],3) : int list * int
```

### See also

[`Lib.butlast`](#Lib.butlast), [`Lib.last`](#Lib.last)
