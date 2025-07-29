## `cons`

``` hol4
Lib.cons : 'a -> 'a list -> 'a list
```

------------------------------------------------------------------------

Curried form of list cons operation.

In some programming situations it is handy to use the "cons" operation
in a curried form. Although it is easy to code up on demand, the `cons`
function is provided for convenience.

### Failure

Never fails.

### Example

``` hol4
- map (cons 1) [[],[2],[2,3]];
> val it = [[1], [1, 2], [1, 2, 3]] : int list list
```
