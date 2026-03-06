## `flatten`

``` hol4
Lib.flatten : 'a list list -> 'a list
```

------------------------------------------------------------------------

Removes one level of bracketing from a list.

An invocation `flatten [[x11,...,x1k1],...,[xn1,...,xnkn]]` yields the
list `[x1,...,x1k1,...,xn1,...,xnkn]`.

### Failure

Never fails.

### Example

``` hol4
- flatten [[1,2,3],[],[4,5]];
> val it = [1, 2, 3, 4, 5] : int list

- flatten ([[[]]] : int list list list);
> val it =  [[]]  : int list list
```
