## `assoc`

``` hol4
hol88Lib.assoc : ''a -> (''a * 'b) list -> ''a * 'b
```

------------------------------------------------------------------------

Searches a list of pairs for a pair whose first component equals a
specified value.

`assoc x [(x1,y1),...,(xn,yn)]` returns the first `(xi,yi)` in the list
such that `xi` equals `x`. The lookup is done on an eqtype, i.e., the
SML implementation must be able to decide equality for the type of `x`.

### Failure

Fails if no matching pair is found. This will always be the case if the
list is empty.

### Example

``` hol4
  - assoc 2 [(1,4),(3,2),(2,5),(2,6)];
 (2, 5) : (int * int)
```

### Comments

Superseded by `Lib.assoc` and `Lib.assoc1`.

### See also

[`hol88Lib.rev_assoc`](#hol88Lib.rev_assoc), [`Lib.assoc`](#Lib.assoc),
[`Lib.assoc1`](#Lib.assoc1)
