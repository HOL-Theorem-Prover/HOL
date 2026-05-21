## `rev_assoc`

``` hol4
Lib.rev_assoc : ''a -> ('b * ''a) list -> 'b
```

------------------------------------------------------------------------

Searches a list of pairs for a pair whose second component equals a
specified value.

An invocation `rev_assoc y [(x1,y1),...,(xn,yn)]` locates the first
`(xi,yi)` in a left-to-right scan of the list such that `yi` equals `y`.
Then `xi` is returned. The lookup is done on an eqtype, i.e., the SML
implementation must be able to decide equality for the type of `y`.

### Failure

Fails if no matching pair is found. This will always be the case if the
list is empty.

### Example

``` hol4
- rev_assoc 2 [(1,4),(3,2),(2,5),(2,6)];
> val it = 3 : int
```

### See also

[`Lib.assoc`](#Lib.assoc), [`Lib.assoc1`](#Lib.assoc1),
[`Lib.assoc2`](#Lib.assoc2), [`Lib.mem`](#Lib.mem),
[`Lib.tryfind`](#Lib.tryfind), [`Lib.exists`](#Lib.exists),
[`Lib.all`](#Lib.all)
