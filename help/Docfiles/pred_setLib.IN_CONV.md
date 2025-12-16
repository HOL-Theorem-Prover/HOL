## `IN_CONV`

``` hol4
pred_setLib.IN_CONV : conv -> conv
```

------------------------------------------------------------------------

Decision procedure for membership in finite sets.

The function `IN_CONV` is a parameterized conversion for proving or
disproving membership assertions of the general form:

``` hol4
   t IN {t1,...,tn}
```

where `{t1;...;tn}` is a set of type `ty->bool` and `t` is a value of
the base type `ty`. The first argument to `IN_CONV` is expected to be a
conversion that decides equality between values of the base type `ty`.
Given an equation `e1 = e2`, where `e1` and `e2` are terms of type `ty`,
this conversion should return the theorem `|- (e1 = e2) = T` or the
theorem `|- (e1 = e2) = F`, as appropriate.

Given such a conversion, the function `IN_CONV` returns a conversion
that maps a term of the form `t IN {t1;...;tn}` to the theorem

``` hol4
   |- t IN {t1;...;tn} = T
```

if `t` is alpha-equivalent to any `ti`, or if the supplied conversion
proves `|- (t = ti) = T` for any `ti`. If the supplied conversion proves
`|- (t = ti) = F` for every `ti`, then the result is the theorem

``` hol4
   |- t IN {t1;...;tn} = F
```

In all other cases, `IN_CONV` will fail.

### Example

In the following example, the conversion `REDUCE_CONV` is supplied as a
parameter and used to test equality of the candidate element `1` with
the actual elements of the given set.

``` hol4
   - IN_CONV REDUCE_CONV ``2 IN {0;SUC 1;3}``;
   > val it = |- 2 IN {0; SUC 1; 3} = T : thm
```

The result is `T` because `REDUCE_CONV` is able to prove that `2` is
equal to `SUC 1`. An example of a negative result is:

``` hol4
   - IN_CONV REDUCE_CONV ``1 IN {0;2;3}``;
   > val it = |- 1 IN {0; 2; 3} = F : thm
```

Finally the behaviour of the supplied conversion is irrelevant when the
value to be tested for membership is alpha-equivalent to an actual
element:

``` hol4
   - IN_CONV NO_CONV ``1 IN {3;2;1}``;
   > val it = |- 1 IN {3; 2; 1} = T : thm
```

The conversion `NO_CONV` always fails, but `IN_CONV` is nontheless able
in this case to prove the required result.

### Failure

`IN_CONV conv` fails if applied to a term that is not of the form
`t IN {t1;...;tn}`. A call `IN_CONV conv t IN {t1;...;tn}` fails unless
the term `t` is alpha-equivalent to some `ti`, or
``` conv ``t = ti`` ``` returns `|- (t = ti) = T` for some `ti`, or
``` conv ``t = ti`` ``` returns `|- (t = ti) = F` for every `ti`.

### See also

[`numLib.REDUCE_CONV`](#numLib.REDUCE_CONV)
