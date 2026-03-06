## `disch`

``` hol4
HolKernel.disch : ((term * term list) -> term list)
```

------------------------------------------------------------------------

Removes those elements of a list of terms that are alpha equivalent to a
given term.

Given a pair `(t,tl)` of term `t` and term list `tl`, `disch` removes
those elements of `tl` that are alpha equivalent to `t`.

### Example

``` hol4
> disch (``\x:bool.T``, [``A = T``, ``B = 3``, ``\y:bool.T``]);
val it = [``A = T``,``B = 3``] : term list
```

### See also

[`Lib.filter`](#Lib.filter)
