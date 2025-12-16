## `enumerate`

``` hol4
Lib.enumerate : int -> 'a list -> (int * 'a) list
```

------------------------------------------------------------------------

Number each element of a list, in ascending order.

An invocation of `enumerate i [x1, ..., xn]` returns the list
`[(i,x1), (i+1,x2), ..., (i+n-1,xn)]`.

### Failure

Never fails.

### Example

``` hol4
- enumerate 0 ["komodo", "iguana", "gecko", "gila"];
> val it = [(0, "komodo"), (1, "iguana"), (2, "gecko"), (3, "gila")]
```
