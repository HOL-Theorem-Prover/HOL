## `int_sort`

``` hol4
Lib.int_sort : int list -> int list
```

------------------------------------------------------------------------

Sorts a list of integers using the `<=` relation.

The call `int_sort list` is equal to `sort (curry (op <=))`. That is, it
is the specialization of `sort` to the usual notion of
less-than-or-equal on ML integers.

### Failure

Never fails.

### Example

A simple example is:

``` hol4
- int_sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9];
> val it = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 7, 8, 9, 9, 9] : int list
```

### Comments

The Standard ML Basis Library also provides implementations of sorting.

### See also

[`Lib.sort`](#Lib.sort)
