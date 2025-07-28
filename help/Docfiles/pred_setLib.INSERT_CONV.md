## `INSERT_CONV` {#pred_setLib.INSERT_CONV}


```
INSERT_CONV : conv -> conv
```



Reduce `t INSERT {t1;...;t;...;tn}` to `{t1;...;t;...;tn}`.


The function `INSERT_CONV` is a parameterized conversion for reducing finite
sets of the form `t INSERT {t1;...;tn}`, where `{t1;...;tn}` is a set of
type `ty->bool` and `t` is equal to some element `ti` of this set.  The first
argument to `INSERT_CONV` is expected to be a conversion that decides equality
between values of the base type `ty`.  Given an equation `e1 = e2`, where
`e1` and `e2` are terms of type `ty`, this conversion should return the theorem
`|- (e1 = e2) = T` or the theorem `|- (e1 = e2) = F`, as appropriate.

Given such a conversion, the function `INSERT_CONV` returns a conversion that
maps a term of the form `t INSERT {t1;...;tn}` to the theorem
    
       |- t INSERT {t1;...;tn} = {t1;...;tn}
    
if `t` is alpha-equivalent to any `ti` in the set `{t1,...,tn}`, or
if the supplied conversion proves `|- (t = ti) = T` for any `ti`.

### Example

In the following example, the conversion `REDUCE_CONV` is supplied as a
parameter and used to test equality of the inserted value `2` with the
remaining elements of the set.
    
       - INSERT_CONV REDUCE_CONV ``2 INSERT {1;SUC 1;3}``;
       > val it = |- {2; 1; SUC 1; 3} = {1; SUC 1; 3} : thm
    
In this example, the supplied conversion `REDUCE_CONV` is able to
prove that `2` is equal to `SUC 1` and the set is therefore reduced.  Note
that `2 INSERT {1; SUC 1; 3}` is just `{2; 1; SUC 1; 3}`.

A call to `INSERT_CONV` fails when the value being inserted is provably not
equal to any of the remaining elements:
    
       - INSERT_CONV REDUCE_CONV ``1 INSERT {2;3}``;
       ! Uncaught exception:
       ! HOL_ERR
    
But this failure can, if desired, be caught using `TRY_CONV`.

The behaviour of the supplied conversion is irrelevant when the inserted value
is alpha-equivalent to one of the remaining elements:
    
       - INSERT_CONV NO_CONV ``y INSERT {x;y;z}``;
       > val it = |- {y; x; y; z} = {x; y; z} : thm
    
The conversion `NO_CONV` always fails, but `INSERT_CONV` is
nontheless able in this case to prove the required result.

Note that `DEPTH_CONV(INSERT_CONV conv)` can be used to remove duplicate
elements from a finite set, but the following conversion is faster:
    
       - fun SETIFY_CONV conv tm =
          (SUB_CONV (SETIFY_CONV conv)
            THENC
           TRY_CONV (INSERT_CONV conv)) tm;
       > val SETIFY_CONV = fn : conv -> conv
    
       - SETIFY_CONV REDUCE_CONV ``{1;2;1;3;2;4;3;5;6}``;
       > val it = |- {1; 2; 1; 3; 2; 4; 3; 5; 6} = {1; 2; 4; 3; 5; 6} : thm
    

### Failure

`INSERT_CONV conv` fails if applied to a term not of the form
`t INSERT {t1;...;tn}`.  A call ``` INSERT_CONV conv ``t INSERT {t1;...;tn} ```
fails unless `t` is alpha-equivalent to some `ti`, or ``` conv ``t = ti`` ``` returns
`|- (t = ti) = T` for some `ti`.

### See also

[`pred_setLib.DELETE_CONV`](#pred_setLib.DELETE_CONV), [`numLib.REDUCE_CONV`](#numLib.REDUCE_CONV)

