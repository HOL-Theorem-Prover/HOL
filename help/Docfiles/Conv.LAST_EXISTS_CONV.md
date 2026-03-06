## `LAST_EXISTS_CONV`

``` hol4
Conv.LAST_EXISTS_CONV : conv -> conv
```

------------------------------------------------------------------------

Applies a conversion to the last existential quantifier (and its body)
in a chain.

Application of `LAST_EXISTS_CONV c` to the term
``` ``?x1 .. xn x. body`` ``` will apply `c` to the term
``` ``?x. body`` ```. If the result of this application is the theorem
`|- (?x. body) = t`, then the result of the whole will be

``` hol4
   |- (?x1 .. xn x. body) = (?x1 .. xn. t)
```

### Failure

Fails if the term is not existentially quantified, or if the conversion
`c` fails when it is applied.

### See also

[`Conv.BINDER_CONV`](#Conv.BINDER_CONV),
[`Conv.LAST_FORALL_CONV`](#Conv.LAST_FORALL_CONV),
[`Conv.STRIP_QUANT_CONV`](#Conv.STRIP_QUANT_CONV)
