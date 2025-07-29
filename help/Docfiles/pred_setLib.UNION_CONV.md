## `UNION_CONV`

``` hol4
pred_setLib.UNION_CONV : conv -> conv
```

------------------------------------------------------------------------

Reduce `{t1;...;tn} UNION s` to `t1 INSERT (... (tn INSERT s))`.

The function `UNION_CONV` is a parameterized conversion for reducing
sets of the form `{t1;...;tn} UNION s`, where `{t1;...;tn}` and `s` are
sets of type `ty->bool`. The first argument to `UNION_CONV` is expected
to be a conversion that decides equality between values of the base type
`ty`. Given an equation `e1 = e2`, where `e1` and `e2` are terms of type
`ty`, this conversion should return the theorem `|- (e1 = e2) = T` or
the theorem `|- (e1 = e2) = F`, as appropriate.

Given such a conversion, the function `UNION_CONV` returns a conversion
that maps a term of the form `{t1;...;tn} UNION s` to the theorem

``` hol4
   |- {t1;...;tn} UNION s = ti INSERT ... (tj INSERT s)
```

where `{ti;...;tj}` is the set of all terms `t` that occur as elements
of `{t1;...;tn}` for which the conversion `IN_CONV conv` fails to prove
that `|- (t IN s) = T` (that is, either by proving `|- (t IN s) = F`
instead, or by failing outright).

### Example

In the following example, `REDUCE_CONV` is supplied as a parameter to
`UNION_CONV` and used to test for membership of each element of the
first finite set `{1;2;3}` of the union in the second finite set
`{SUC 0;3;4}`.

``` hol4
   - UNION_CONV REDUCE_CONV (Term`{1;2;3} UNION {SUC 0;3;4}`);
   > val it = |- {1; 2; 3} UNION {SUC 0; 3; 4} = {2; SUC 0; 3; 4} : thm
```

The result is `{2;SUC 0;3;4}`, rather than `{1;2;SUC 0;3;4}`, because
`UNION_CONV` is able by means of a call to

``` hol4
   - IN_CONV REDUCE_CONV (Term`1 IN {SUC 0;3;4}`);
```

to prove that `1` is already an element of the set `{SUC 0;3;4}`.

The conversion supplied to `UNION_CONV` need not actually prove equality
of elements, if simplification of the resulting set is not desired. For
example:

``` hol4
   - UNION_CONV NO_CONV ``{1;2;3} UNION {SUC 0;3;4}``;
   > val it = |- {1;2;3} UNION {SUC 0;3;4} = {1;2;SUC 0;3;4} : thm
```

In this case, the resulting set is just left unsimplified. Moreover, the
second set argument to `UNION` need not be a finite set:

``` hol4
   - UNION_CONV NO_CONV ``{1;2;3} UNION s``;
   > val it = |- {1;2;3} UNION s = 1 INSERT (2 INSERT (3 INSERT s)) : thm
```

And, of course, in this case the conversion argument to `UNION_CONV` is
irrelevant.

### Failure

`UNION_CONV conv` fails if applied to a term not of the form
`{t1;...;tn} UNION s`.

### See also

[`pred_setLib.IN_CONV`](#pred_setLib.IN_CONV),
[`numLib.REDUCE_CONV`](#numLib.REDUCE_CONV)
