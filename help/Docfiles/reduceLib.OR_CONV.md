## `OR_CONV`

``` hol4
reduceLib.OR_CONV : conv
```

------------------------------------------------------------------------

Simplifies certain boolean disjunction expressions.

If `tm` corresponds to one of the forms given below, where `t` is an
arbitrary term of type `bool`, then `OR_CONV tm` returns the
corresponding theorem. Note that in the last case the disjuncts need
only be alpha-equivalent rather than strictly identical.

``` hol4
   OR_CONV "T \/ t" = |- T \/ t = T
   OR_CONV "t \/ T" = |- t \/ T = T
   OR_CONV "F \/ t" = |- F \/ t = t
   OR_CONV "t \/ F" = |- t \/ F = t
   OR_CONV "t \/ t" = |- t \/ t = t
```

### Failure

`OR_CONV tm` fails unless `tm` has one of the forms indicated above.

### Example

``` hol4
#OR_CONV "F \/ T";;
|- F \/ T = T

#OR_CONV "X \/ F";;
|- X \/ F = X

#OR_CONV "(!n. n + 1 = SUC n) \/ (!m. m + 1 = SUC m)";;
|- (!n. n + 1 = SUC n) \/ (!m. m + 1 = SUC m) = (!n. n + 1 = SUC n)
```
