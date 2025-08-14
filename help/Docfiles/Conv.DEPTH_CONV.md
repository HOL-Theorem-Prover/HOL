## `DEPTH_CONV`

``` hol4
Conv.DEPTH_CONV : conv -> conv
```

------------------------------------------------------------------------

Applies a conversion repeatedly to all the sub-terms of a term, in
bottom-up order.

`DEPTH_CONV c tm` repeatedly applies the conversion `c` to all the
subterms of the term `tm`, including the term `tm` itself. The supplied
conversion is applied repeatedly (zero or more times, as is done by
`REPEATC`) to each subterm until it fails. The conversion is applied to
subterms in bottom-up order.

### Failure

`DEPTH_CONV c tm` never fails but can diverge if the conversion `c` can
be applied repeatedly to some subterm of `tm` without failing.

### Example

The following example shows how `DEPTH_CONV` applies a conversion to all
subterms to which it applies:

``` hol4
   - DEPTH_CONV BETA_CONV (Term `(\x. (\y. y + x) 1) 2`);
   > val it = |- (\x. (\y. y + x)1)2 = 1 + 2 : thm
```

Here, there are two beta-redexes in the input term, one of which occurs
within the other. `DEPTH_CONV BETA_CONV` applies beta-conversion to
innermost beta-redex `(\y. y + x) 1` first. The outermost beta-redex is
then `(\x. 1 + x) 2`, and beta-conversion of this redex gives `1 + 2`.

Because `DEPTH_CONV` applies a conversion bottom-up, the final result
may still contain subterms to which the supplied conversion applies. For
example, in:

``` hol4
   - DEPTH_CONV BETA_CONV (Term `(\f x. (f x) + 1) (\y.y) 2`);
   > val it = |- (\f x. (f x) + 1)(\y. y)2 = ((\y. y)2) + 1 : thm
```

the right-hand side of the result still contains a beta-redex, because
the redex `(\y.y)2` is introduced by virtue of an application of
`BETA_CONV` higher-up in the structure of the input term. By contrast,
in the example:

``` hol4
   - DEPTH_CONV BETA_CONV (Term `(\f x. (f x)) (\y.y) 2`);
   > val it = |- (\f x. f x)(\y. y)2 = 2 : thm
```

all beta-redexes are eliminated, because `DEPTH_CONV` repeats the
supplied conversion (in this case, `BETA_CONV`) at each subterm (in this
case, at the top-level term).

If the conversion `c` implements the evaluation of a function in logic,
then `DEPTH_CONV c` will do bottom-up evaluation of nested applications
of it. For example, the conversion `ADD_CONV` implements addition of
natural number constants within the logic. Thus, the effect of:

``` hol4
   - DEPTH_CONV reduceLib.ADD_CONV (Term `(1 + 2) + (3 + 4 + 5)`);
   > val it = |- (1 + 2) + (3 + (4 + 5)) = 15 : thm
```

is to compute the sum represented by the input term.

### Comments

The implementation of this function uses failure to avoid rebuilding
unchanged subterms. That is to say, during execution the exception
`QConv.UNCHANGED` may be generated and later trapped. The behaviour of
the function is dependent on this use of failure. So, if the conversion
given as an argument happens to generate the same exception, the
operation of `DEPTH_CONV` will be unpredictable.

### See also

[`Conv.ONCE_DEPTH_CONV`](#Conv.ONCE_DEPTH_CONV),
[`Conv.REDEPTH_CONV`](#Conv.REDEPTH_CONV),
[`Conv.TOP_DEPTH_CONV`](#Conv.TOP_DEPTH_CONV)
