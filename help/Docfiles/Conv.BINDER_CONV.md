## `BINDER_CONV`

``` hol4
Conv.BINDER_CONV : conv -> conv
```

------------------------------------------------------------------------

Applies a conversion underneath a binder.

If `conv N` returns `A |- N = P`, then `BINDER_CONV conv (M (\v.N))`
returns `A |- M (\v.N) = M (\v.P)` and `BINDER_CONV conv (\v.N)` returns
`A |- (\v.N) = (\v.P)`

### Failure

If `conv N` fails, or if `v` is free in `A`.

### Example

``` hol4
- BINDER_CONV SYM_CONV (Term `\x. x + 0 = x`);
> val it = |- (\x. x + 0 = x) = \x. x = x + 0 : thm
```

### Comments

For deeply nested quantifiers, `STRIP_BINDER_CONV` and
`STRIP_QUANT_CONV` are more efficient than iterated application of
`BINDER_CONV`, `BINDER_CONV`, or `ABS_CONV`.

### See also

[`Conv.QUANT_CONV`](#Conv.QUANT_CONV),
[`Conv.STRIP_QUANT_CONV`](#Conv.STRIP_QUANT_CONV),
[`Conv.STRIP_BINDER_CONV`](#Conv.STRIP_BINDER_CONV),
[`Conv.ABS_CONV`](#Conv.ABS_CONV)
