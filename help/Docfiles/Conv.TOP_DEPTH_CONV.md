## `TOP_DEPTH_CONV` {#Conv.TOP_DEPTH_CONV}


```
TOP_DEPTH_CONV : (conv -> conv)
```



Applies a conversion top-down to all subterms, retraversing changed ones.


`TOP_DEPTH_CONV c tm` repeatedly applies the conversion `c` to all the subterms
of the term `tm`, including the term `tm` itself. The supplied conversion `c`
is applied to the subterms of `tm` in top-down order and is applied repeatedly
(zero or more times, as is done by `REPEATC`) at each subterm until it fails.
If a subterm `t` is changed (up to alpha-equivalence) by virtue of the
application of `c` to its own subterms, then the term into which `t` is
transformed is retraversed by applying `TOP_DEPTH_CONV c` to it.

### Failure

`TOP_DEPTH_CONV c tm` never fails but can diverge.

### Comments

The implementation of this function uses failure to avoid rebuilding
unchanged subterms. That is to say, during execution the exception
`QConv.UNCHANGED` may be generated and later trapped. The behaviour of
the function is dependent on this use of failure. So, if the
conversion given as an argument happens to generate the same
exception, the operation of `TOP_DEPTH_CONV` will be unpredictable.

### See also

[`Conv.DEPTH_CONV`](#Conv.DEPTH_CONV), [`Conv.ONCE_DEPTH_CONV`](#Conv.ONCE_DEPTH_CONV), [`Conv.REDEPTH_CONV`](#Conv.REDEPTH_CONV)

