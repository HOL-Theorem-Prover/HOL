## `upto`

``` hol4
Lib.upto : int -> int -> int list
```

------------------------------------------------------------------------

Builds a list of integers.

An invocation `upto b t` returns the list `[b, b+1, ..., t]`, if
`b <= t`. Otherwise, the empty list is returned.

### Failure

Never fails.

### Example

``` hol4
- upto 2 10;
> val it = [2,3,4,5,6,7,8,9,10]
```
