## `NEGATE_CONV`

``` hol4
Arith.NEGATE_CONV : (conv -> conv)
```

------------------------------------------------------------------------

Function for negating the operation of a conversion that proves a
formula to be either true or false.

This function negates the operation of a conversion that proves a
formula to be either true or false. For example, if `conv` proves `"t"`
to be equal to `"T"` then `NEGATE_CONV conv` will prove `"~t"` to be
`"F"`.

### Failure

Fails if the application of the conversion to the negation of the
formula does not yield either `"T"` or `"F"`.

### Example

``` hol4
#ARITH_CONV "!n. 0 <= n";;
|- (!n. 0 <= n) = T

#NEGATE_CONV ARITH_CONV "~(!n. 0 <= n)";;
|- ~(!n. 0 <= n) = F

#NEGATE_CONV ARITH_CONV "?n. ~(0 <= n)";;
|- (?n. ~0 <= n) = F
```
