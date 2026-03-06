## `equal`

``` hol4
Lib.equal : ''a -> ''a -> bool
```

------------------------------------------------------------------------

Curried form of ML equality.

In some programming situations it is useful to use equality in a curried
form. Although it is easy to code up on demand, the `equal` function is
provided for convenience.

### Failure

Never fails.

### Example

``` hol4
- filter (equal 1) [1,2,1,4,5];
> val it = [1, 1] : int list
```
