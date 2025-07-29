## `REPEATC`

``` hol4
Conv.REPEATC : conv -> conv
```

------------------------------------------------------------------------

Repeatedly apply a conversion (zero or more times) until it fails.

If `c` is a conversion effects a transformation of a term `t` to a term
`t'`, that is if `c` maps `t` to the theorem `` |- t = t` ``, then
`REPEATC c` is the conversion that repeats this transformation as often
as possible. More exactly, if `c` maps the term ``` ``ti`` ``` to
`|- ti=t(i+1)` for `i` from `1` to `n`, but fails when applied to the
`n+1`th term ``` ``t(n+1)`` ```, then ``` REPEATC c ``t1`` ``` returns
`|- t1 = t(n+1)`. And if ``` c ``t`` ``` fails, them
``` REPEATC c ``t`` ``` returns `|- t = t`.

Further, if ``` c ``t`` ``` raises the `UNCHANGED` exception, then
``` REPEATC c ``t`` ``` also raises the same exception (rather than go
into an infinite loop).

### Failure

Never fails, but can diverge if the supplied conversion never fails.
