## `ONCE_DEPTH_CONV`

``` hol4
Conv.ONCE_DEPTH_CONV : (conv -> conv)
```

------------------------------------------------------------------------

Applies a conversion once to the first suitable sub-term(s) encountered
in top-down order.

`ONCE_DEPTH_CONV c tm` applies the conversion `c` once to the first
subterm or subterms encountered in a top-down 'parallel' search of the
term `tm` for which `c` succeeds. If the conversion `c` fails on all
subterms of `tm`, the theorem returned is `|- tm = tm`.

### Failure

Never fails.

### Example

The following example shows how `ONCE_DEPTH_CONV` applies a conversion
to only the first suitable subterm(s) found in a top-down search:

``` hol4
   - ONCE_DEPTH_CONV BETA_CONV (Term `(\x. (\y. y + x) 1) 2`);
   > val it = |- (\x. (\y. y + x)1)2 = (\y. y + 2) 1 : thm
```

Here, there are two beta-redexes in the input term. One of these occurs
within the other, so `BETA_CONV` is applied only to the outermost one.

Note that the supplied conversion is applied by `ONCE_DEPTH_CONV` to all
independent subterms at which it succeeds. That is, the conversion is
applied to every suitable subterm not contained in some other subterm
for which the conversions also succeeds, as illustrated by the following
example:

``` hol4
   - ONCE_DEPTH_CONV numLib.num_CONV (Term `(\x. (\y. y + x) 1) 2`);
   > val it = |- (\x. (\y. y + x)1)2 = (\x. (\y. y + x)(SUC 0))(SUC 1) : thm
```

Here `num_CONV` is applied to both `1` and `2`, since neither term
occurs within a larger subterm for which the conversion `num_CONV`
succeeds.

`ONCE_DEPTH_CONV` is frequently used when there is only one subterm to
which the desired conversion applies. This can be much faster than using
other functions that attempt to apply a conversion to all subterms of a
term (e.g. `DEPTH_CONV`). If, for example, the current goal in a
goal-directed proof contains only one beta-redex, and one wishes to
apply `BETA_CONV` to it, then the tactic

``` hol4
   CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)
```

may, depending on where the beta-redex occurs, be much faster than

``` hol4
   CONV_TAC (TOP_DEPTH_CONV BETA_CONV)
```

`ONCE_DEPTH_CONV c` may also be used when the supplied conversion `c`
never fails, in which case using a conversion such as `DEPTH_CONV c`,
which applies `c` repeatedly would never terminate.

### Comments

The implementation of this function uses failure to avoid rebuilding
unchanged subterms. That is to say, during execution the exception
`QConv.UNCHANGED` may be generated and later trapped. The behaviour of
the function is dependent on this use of failure. So, if the conversion
given as an argument happens to generate the same exception, the
operation of `ONCE_DEPTH_CONV` will be unpredictable.

### See also

[`Conv.DEPTH_CONV`](#Conv.DEPTH_CONV),
[`Conv.REDEPTH_CONV`](#Conv.REDEPTH_CONV),
[`Conv.TOP_DEPTH_CONV`](#Conv.TOP_DEPTH_CONV)
