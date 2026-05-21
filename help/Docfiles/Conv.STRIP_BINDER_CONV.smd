## `STRIP_BINDER_CONV`

``` hol4
Conv.STRIP_BINDER_CONV : term option -> conv -> conv
```

------------------------------------------------------------------------

Applies a conversion underneath a binder prefix.

If the application of `conv` to `M` yields `|- M = N`, then
`STRIP_BINDER_CONV (SOME c) conv (c(\v1. ... (c(\vn.M))...))` returns
`|- c(\v1. ... (c(\vn.M))...) = c(\v1. ... (c(\vn.N))...)` and
`STRIP_BINDER_CONV NONE conv (\v1 ... vn.M)` returns
`|- (\v1 ... vn.M) = (\v1 ... vn.N)`.

### Failure

If `conv M` fails. Also fails if some of `[v1,...,vn]` are free in the
hypotheses of `conv M`.

### Example

``` hol4
- STRIP_BINDER_CONV NONE BETA_CONV (Term `\u v w. (\a. a + v * w) u`);
> val it = |- (\u v w. (\a. a + v * w) u) = (\u v w. u + v * w) : thm

- STRIP_BINDER_CONV (SOME existential) SYM_CONV
                    (Term `?u v w x y. u + v = w + x + y`);
> val it = |- (?u v w x y. u + v = w + x + y) =
               ?u v w x y. w + x + y = u + v : thm
```

### Comments

`STRIP_BINDER_CONV` is more efficient than iterated application of
`BINDER_CONV` or `ABS_CONV` or `QUANT_CONV`.

### See also

[`Conv.BINDER_CONV`](#Conv.BINDER_CONV),
[`Conv.ABS_CONV`](#Conv.ABS_CONV),
[`Conv.QUANT_CONV`](#Conv.QUANT_CONV),
[`Conv.STRIP_BINDER_CONV`](#Conv.STRIP_BINDER_CONV),
[`Conv.STRIP_QUANT_CONV`](#Conv.STRIP_QUANT_CONV)
