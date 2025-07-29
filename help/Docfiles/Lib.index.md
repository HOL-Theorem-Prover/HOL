## `index`

``` hol4
Lib.index : ('a -> bool) -> 'a list -> int
```

------------------------------------------------------------------------

Finds index of first list element for which predicate holds.

An application `index P l` returns the index (0-based) to the first
element (in a left-to-right scan) of `l` that `P` holds of.

### Failure

If `P` doesn't hold of any element of `l`, then `index P l` fails. If
`P x` fails for any `x` encountered in the scan, then `index P l` fails.

### Example

``` hol4
- index (equal 3) [1,2,3];
> val it = 2 : int

- let fun even i = (i mod 2 = 0)
  in try (index even) [1,3,5,7,9]
  end;

Exception raised at Lib.index:
no such element
! Uncaught exception:
! HOL_ERR

- index (equal 3 o hd) [[1],[],[2,3]];
! Uncaught exception:
! Empty
```

### See also

[`Lib.el`](#Lib.el)
