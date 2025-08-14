## `assoc1`

``` hol4
Lib.assoc1 : ''a -> (''a * 'b) list -> (''a * 'b)option
```

------------------------------------------------------------------------

Searches a list of pairs for a pair whose first component equals a
specified value.

`assoc1 x [(x1,y1),...,(xn,yn)]` returns `SOME (xi,yi)` for the first
pair `(xi,yi)` in the list such that `xi` equals `x`. Otherwise, `NONE`
is returned. The lookup is done on an eqtype, i.e., the SML
implementation must be able to decide equality for the type of `x`.

### Failure

Never fails.

### Example

``` hol4
- assoc1 2 [(1,4),(3,2),(2,5),(2,6)];
> val it = SOME (2, 5) : (int * int)option
```

### See also

[`Lib.assoc`](#Lib.assoc), [`Lib.assoc2`](#Lib.assoc2),
[`Lib.rev_assoc`](#Lib.rev_assoc), [`Lib.mem`](#Lib.mem),
[`Lib.tryfind`](#Lib.tryfind), [`Lib.exists`](#Lib.exists),
[`Lib.all`](#Lib.all)
