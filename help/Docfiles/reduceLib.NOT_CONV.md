## `NOT_CONV`

``` hol4
reduceLib.NOT_CONV : conv
```

------------------------------------------------------------------------

Simplifies certain boolean negation expressions.

If `tm` corresponds to one of the forms given below, where `t` is an
arbitrary term of type `bool`, then `NOT_CONV tm` returns the
corresponding theorem.

``` hol4
   NOT_CONV "~F"  = |-  ~F = T
   NOT_CONV "~T"  = |-  ~T = F
   NOT_CONV "~~t" = |- ~~t = t
```

### Failure

`NOT_CONV tm` fails unless `tm` has one of the forms indicated above.

### Example

``` hol4
#NOT_CONV "~~~~T";;
|- ~~~~T = ~~T

#NOT_CONV "~~T";;
|- ~~T = T

#NOT_CONV "~T";;
|- ~T = F
```
