## `BEQ_CONV`

``` hol4
reduceLib.BEQ_CONV : conv
```

------------------------------------------------------------------------

Simplifies certain expressions involving boolean equality.

If `tm` corresponds to one of the forms given below, where `t` is an
arbitrary term of type `bool`, then `BEQ_CONV tm` returns the
corresponding theorem. Note that in the last case the left-hand and
right-hand sides need only be alpha-equivalent rather than strictly
identical.

``` hol4
   BEQ_CONV "T = t" = |- T = t = t
   BEQ_CONV "t = T" = |- t = T = t
   BEQ_CONV "F = t" = |- F = t = ~t
   BEQ_CONV "t = F" = |- t = F = ~t
   BEQ_CONV "t = t" = |- t = t = T
```

### Failure

`BEQ_CONV tm` fails unless `tm` has one of the forms indicated above.

### Example

``` hol4
#BEQ_CONV "T = T";;
|- (T = T) = T

#BEQ_CONV "F = T";;
|- (F = T) = F

#BEQ_CONV "(!x:*#**. x = (FST x,SND x)) = (!y:*#**. y = (FST y,SND y))";;
|- ((!x. x = FST x,SND x) = (!y. y = FST y,SND y)) = T
```
