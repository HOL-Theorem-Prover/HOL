## `COND_CONV`

``` hol4
reduceLib.COND_CONV : conv
```

------------------------------------------------------------------------

Simplifies certain conditional expressions.

If `tm` corresponds to one of the forms given below, where `b` has type
`bool` and `t1` and `t2` have the same type, then `COND_CONV tm` returns
the corresponding theorem. Note that in the last case the arms need only
be alpha-equivalent rather than strictly identical.

``` hol4
   COND_CONV "F => t1 | t2" = |- (T => t1 | t2) = t2
   COND_CONV "T => t1 | t2" = |- (T => t1 | t2) = t1
   COND_CONV "b => t | t    = |- (b => t | t) = t
```

### Failure

`COND_CONV tm` fails unless `tm` has one of the forms indicated above.

### Example

``` hol4
#COND_CONV "F => F | T";;
|- (F => F | T) = T

#COND_CONV "T => F | T";;
|- (T => F | T) = F

#COND_CONV "b => (\x. SUC x) | (\p. SUC p)";;
|- (b => (\x. SUC x) | (\p. SUC p)) = (\x. SUC x)
```
