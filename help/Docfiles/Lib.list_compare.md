## `list_compare`

``` hol4
Lib.list_compare : 'a cmp -> 'a list cmp
```

------------------------------------------------------------------------

Lifts a comparison function to a lexicographic ordering on lists.

An application `list_compare comp (L1,L2)` uses `comp` as a basis for
comparing the lists `L1` and `L2` lexicographically, in left-to-right
order. The returned value is one of `{LESS, EQUAL, GREATER}`.

### Failure

If `comp` fails when applied to corresponding elements of `L1` and `L2`.

### Example

``` hol4
- list_compare Int.compare ([1,2,3,4], [1,2,3,4]);
> val it = EQUAL : order

- list_compare Int.compare ([1,2,3,4], [1,2,3,4,5]);
> val it = LESS : order

- list_compare Int.compare ([1,2,3,4], [1,2,3,2]);
> val it = GREATER : order
```
