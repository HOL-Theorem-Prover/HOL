## `REDEPTH_CONV`

``` hol4
Conv.REDEPTH_CONV : (conv -> conv)
```

------------------------------------------------------------------------

Applies a conversion bottom-up to all subterms, retraversing changed
ones.

`REDEPTH_CONV c tm` applies the conversion `c` repeatedly to all
subterms of the term `tm` and recursively applies `REDEPTH_CONV c` to
each subterm at which `c` succeeds, until there is no subterm remaining
for which application of `c` succeeds.

More precisely, `REDEPTH_CONV c tm` repeatedly applies the conversion
`c` to all the subterms of the term `tm`, including the term `tm`
itself. The supplied conversion `c` is applied to the subterms of `tm`
in bottom-up order and is applied repeatedly (zero or more times, as is
done by `REPEATC`) to each subterm until it fails. If `c` is
successfully applied at least once to a subterm, `t` say, then the term
into which `t` is transformed is retraversed by applying
`REDEPTH_CONV c` to it.

### Failure

`REDEPTH_CONV c tm` never fails but can diverge if the conversion `c`
can be applied repeatedly to some subterm of `tm` without failing.

### Example

The following example shows how `REDEPTH_CONV` retraverses subterms:

``` hol4
   - REDEPTH_CONV BETA_CONV (Term `(\f x. (f x) + 1) (\y.y) 2`);
   val it = |- (\f x. (f x) + 1)(\y. y)2 = 2 + 1 : thm
```

Here, `BETA_CONV` is first applied successfully to the (beta-redex)
subterm:

``` hol4
   (\f x. (f x) + 1) (\y.y)
```

This application reduces this subterm to:

``` hol4
   (\x. ((\y.y) x) + 1)
```

`REDEPTH_CONV BETA_CONV` is then recursively applied to this transformed
subterm, eventually reducing it to `(\x. x + 1)`. Finally, a
beta-reduction of the top-level term, now the simplified beta-redex
`(\x. x + 1) 2`, produces `2 + 1`.

### Comments

The implementation of this function uses failure to avoid rebuilding
unchanged subterms. That is to say, during execution the exception
`QConv.UNCHANGED` may be generated and later trapped. The behaviour of
the function is dependent on this use of failure. So, if the conversion
given as an argument happens to generate the same exception, the
operation of `REDEPTH_CONV` will be unpredictable.

### See also

[`Conv.DEPTH_CONV`](#Conv.DEPTH_CONV),
[`Conv.ONCE_DEPTH_CONV`](#Conv.ONCE_DEPTH_CONV),
[`Conv.TOP_DEPTH_CONV`](#Conv.TOP_DEPTH_CONV)
