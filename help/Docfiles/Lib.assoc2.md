## `assoc2`

``` hol4
Lib.assoc2 : ''a -> ('b * ''a) list -> ('b * ''a)option
```

------------------------------------------------------------------------

Searches a list of pairs for a pair whose second component equals a
specified value.

An invocation `assoc2 y [(x1,y1),...,(xn,yn)]` returns `SOME (xi,yi)`
for the first `(xi,yi)` in the list such that `yi` equals `y`.
Otherwise, `NONE` is returned. The lookup is done on an eqtype, i.e.,
the SML implementation must be able to decide equality for the type of
`y`.

### Failure

Never fails.

### Example

``` hol4
- assoc2 2 [(1,4),(3,2),(2,5),(2,6)];
> val it = SOME (3, 2) : (int * int) option
```

### See also

[`Lib.assoc`](#Lib.assoc), [`Lib.assoc1`](#Lib.assoc1),
[`Lib.rev_assoc`](#Lib.rev_assoc), [`Lib.mem`](#Lib.mem),
[`Lib.tryfind`](#Lib.tryfind), [`Lib.exists`](#Lib.exists),
[`Lib.all`](#Lib.all)
