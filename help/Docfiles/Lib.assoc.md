## `assoc`

``` hol4
Lib.assoc : ''a -> (''a * 'b) list -> 'b
```

------------------------------------------------------------------------

Searches a list of pairs for a pair whose first component equals a
specified value, then returns the second component of the pair.

`assoc x [(x1,y1),...,(xn,yn)]` locates the first `(xi,yi)` in a
left-to-right scan of the list such that `xi` equals `x`. Then `yi` is
returned. The lookup is done on an eqtype, i.e., the SML implementation
must be able to decide equality for the type of `x`.

### Failure

Fails if no matching pair is found. This will always be the case if the
list is empty.

### Example

``` hol4
- assoc 2 [(1,4),(3,2),(2,5),(2,6)];
> val it = 5 : int
```

### See also

[`Lib.assoc1`](#Lib.assoc1), [`Lib.assoc2`](#Lib.assoc2),
[`Lib.rev_assoc`](#Lib.rev_assoc), [`Lib.mem`](#Lib.mem),
[`Lib.tryfind`](#Lib.tryfind), [`Lib.exists`](#Lib.exists),
[`Lib.all`](#Lib.all)
