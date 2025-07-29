## `RIGHT_CONV_RULE`

``` hol4
Conv.RIGHT_CONV_RULE : (conv -> thm -> thm)
```

------------------------------------------------------------------------

Applies a conversion to the right-hand side of an equational theorem.

If `c` is a conversion that maps a term `"t2"` to the theorem
`|- t2 = t2'`, then the rule `RIGHT_CONV_RULE c` infers `|- t1 = t2'`
from the theorem `|- t1 = t2`. That is, if `c "t2"` returns
`A' |- t2 = t2'`, then:

``` hol4
       A |- t1 = t2
   ---------------------  RIGHT_CONV_RULE c
    A u A' |- t1 = t2'
```

Note that if the conversion `c` returns a theorem with assumptions, then
the resulting inference rule adds these to the assumptions of the
theorem it returns.

### Failure

`RIGHT_CONV_RULE c th` fails if the conclusion of the theorem `th` is
not an equation, or if `th` is an equation but `c` fails when applied
its right-hand side. The function returned by `RIGHT_CONV_RULE c` will
also fail if the ML function `c:term->thm` is not, in fact, a conversion
(i.e. a function that maps a term `t` to a theorem `|- t = t'`).

### See also

[`Conv.CONV_RULE`](#Conv.CONV_RULE)
