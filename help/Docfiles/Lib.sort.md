## `sort`

``` hol4
Lib.sort : ('a -> 'a -> bool) -> 'a list -> 'a list
```

------------------------------------------------------------------------

Sorts a list using a given transitive 'ordering' relation.

The call `sort opr list` where `opr` is a curried transitive relation on
the elements of `list`, will sort the list, i.e., will permute `list`
such that if `x opr y` but not `y opr x` then `x` will occur to the left
of `y` in the sorted list. In particular if `opr` is a total order, the
result list will be sorted in the usual sense of the word.

### Failure

Never fails.

### Example

A simple example is:

``` hol4
   - sort (curry (op<)) [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9];
   > val it = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 7, 8, 9, 9, 9] : int list
```

The following example is a little more complicated. Note that the
'ordering' is not antisymmetric.

``` hol4
   - sort (curry (op< o (fst ## fst)))
          [(1,3), (7,11), (3,2), (3,4), (7,2), (5,1)];
   > val it = [(1,3), (3,4), (3,2), (5,1), (7,2), (7,11)] : (int * int) list
```

### Comments

The Standard ML Basis Library also provides implementations of sorting.

### See also

[`Lib.int_sort`](#Lib.int_sort), [`Lib.topsort`](#Lib.topsort)
