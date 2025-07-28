## `DELETE_CONV` {#pred_setLib.DELETE_CONV}


```
DELETE_CONV : conv -> conv
```



Reduce `{t1;...;tn} DELETE t` by deleting `t` from  `{t1;...;tn}`.


The function `DELETE_CONV` is a parameterized conversion for reducing finite
sets of the form `{t1;...;tn} DELETE t`, where the term `t` and the
elements of `{t1;...;tn}` are of some base type `ty`.  The first argument to
`DELETE_CONV` is expected to be a conversion that decides equality between
values of the base type `ty`.  Given an equation `e1 = e2`, where `e1` and
`e2` are terms of type `ty`, this conversion should return the theorem
`|- (e1 = e2) = T` or the theorem `|- (e1 = e2) = F`, as appropriate.

Given such a conversion `conv`, the function `DELETE_CONV` returns a
conversion that maps a term of the form `{t1;...;tn} DELETE t` to the
theorem
    
       |- {t1;...;tn} DELETE t = {ti;...;tj}
    
where `{ti;...;tj}` is the subset of `{t1;...;tn}` for which
the supplied equality conversion `conv` proves
    
       |- (ti = t) = F, ..., |- (tj = t) = F
    
and for all the elements `tk` in `{t1;...;tn}` but not in
`{ti;...;tj}`, either `conv` proves `|- (tk = t) = T` or `tk` is
alpha-equivalent to `t`.  That is, the reduced set `{ti;...;tj}` comprises
all those elements of the original set that are provably not equal to the
deleted element `t`.

### Example

In the following example, the conversion `REDUCE_CONV` is supplied as a
parameter and used to test equality of the deleted value `2` with the
elements of the set.
    
       - DELETE_CONV REDUCE_CONV ``{2; 1; SUC 1; 3} DELETE 2``;
       > val it = |- {2; 1; SUC 1; 3} DELETE 2 = {1; 3} : thm
    
‘

### Failure

`DELETE_CONV conv` fails if applied to a term not of the form
`{t1;...;tn} DELETE t`.  A call ``` DELETE_CONV conv ``{t1;...;tn} DELETE t`` ```
fails unless for each element `ti` of the set `{t1;...;tn}`, the
term `t` is either alpha-equivalent to `ti` or ``` conv ``ti = t`` ``` returns
`|- (ti = t) = T` or `|- (ti = t) = F`.

### See also

[`pred_setLib.INSERT_CONV`](#pred_setLib.INSERT_CONV), [`numLib.REDUCE_CONV`](#numLib.REDUCE_CONV)

