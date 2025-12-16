## `append`

``` hol4
Lib.append : 'a list -> 'a list -> 'a list
```

------------------------------------------------------------------------

Curried form of list append.

The function `append` is a curried form of the standard operation for
appending two ML lists.

### Failure

Never fails.

### Example

``` hol4
- append [1] [2,3] = [1] @ [2,3];
> val it = true : bool
```
