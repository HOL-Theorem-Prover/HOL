## `rev_assoc`

``` hol4
hol88Lib.rev_assoc : ''a -> ('b * ''a) list -> 'b * ''a
```

------------------------------------------------------------------------

Searches a list of pairs for a pair whose second component equals a
specified value.

`rev_assoc y [(x1,y1),...,(xn,yn)]` returns the first `(xi,yi)` in the
list such that `yi` equals `y`. The lookup is done on an eqtype, i.e.,
the SML implementation must be able to decide equality for the type of
`y`.

### Failure

Fails if no matching pair is found. This will always be the case if the
list is empty.

### Example

``` hol4
  - rev_assoc 2 [(1,4),(3,2),(2,5),(2,6)];
  (3, 2) : (int * int)
```

### Comments

Superseded by `Lib.rev_assoc` and `Lib.assoc2`.

### See also

[`hol88Lib.assoc`](#hol88Lib.assoc), [`Lib.rev_assoc`](#Lib.rev_assoc),
[`Lib.assoc2`](#Lib.assoc2)
