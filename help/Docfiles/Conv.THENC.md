## `THENC`

``` hol4
op Conv.THENC : (conv -> conv -> conv)
```

------------------------------------------------------------------------

Applies two conversions in sequence.

If the conversion `c1` returns `|- t = t'` when applied to a term
``` ``t`` ```, and `c2` returns `|- t' = t''` when applied to
``` ``t'`` ```, then the composite conversion
``` (c1 THENC c2) ``t`` ``` returns `|- t = t''`. That is,
``` (c1 THENC c2) ``t`` ``` has the effect of transforming the term
``` ``t`` ``` first with the conversion `c1` and then with the
conversion `c2`.

`THENC` also handles the possibility that either of its arguments might
return the `UNCHANGED` exception. If the first conversion returns
`UNCHANGED` when applied to its argument, `THENC` just returns the
result of the second conversion applied to the same initial term. If the
second conversion raises `UNCHANGED` (and the first did not), then the
result will be the theorem returned by the first conversion. In this
way, unnecessary calls to `TRANS` can be avoided.

### Failure

(This refers to failure other than by raising `UNCHANGED`).
``` (c1 THENC c2) ``t`` ``` fails if either the conversion `c1` fails
when applied to ``` ``t`` ```, or if ``` c1 ``t`` ``` succeeds and
returns `|- t = t'` but `c2` fails when applied to ``` ``t'`` ```.
``` (c1 THENC c2) ``t`` ``` may also fail if either of `c1` or `c2` is
not, in fact, a conversion (i.e. a function that maps a term `t` to a
theorem `|- t = t'`).

### See also

[`Conv.UNCHANGED`](#Conv.UNCHANGED),
[`Conv.EVERY_CONV`](#Conv.EVERY_CONV)
