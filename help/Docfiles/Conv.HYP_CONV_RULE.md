## `HYP_CONV_RULE`

``` hol4
Conv.HYP_CONV_RULE : (term -> bool) -> (conv -> thm -> thm)
```

------------------------------------------------------------------------

Makes an inference rule by applying a conversion to hypotheses of a
theorem.

If `conv` is a conversion, then `HYP_CONV_RULE sel conv` is an inference
rule that applies `conv` to those hypotheses of a theorem which are
selected by `sel`. That is, if `conv` maps a term `"h"` to the theorem
`|- h = h'`, then the rule `HYP_CONV_RULE sel conv` infers `A, h' |- c`
from the theorem `A, h |- c`. More precisely, if `conv "h"` returns
`A' |- h = h'`, then:

``` hol4
       A, h |- c
   ----------------  HYP_CONV_RULE sel conv
    A u A', h' |- c
```

Note that if the conversion `conv` returns a theorem with assumptions,
then the resulting inference rule adds these to the assumptions of the
theorem it returns.

### Failure

`HYP_CONV_RULE sel conv th` fails if `sel` fails when applied to a
hypothesis of `th`, or if `conv` fails when applied to a hypothesis
selected by `sel`. The function returned by `HYP_CONV_RULE sel conv`
will also fail if the ML function `conv:term->thm` is not, in fact, a
conversion (i.e. a function that maps a term `h` to a theorem
`|- h = h'`).

### See also

[`Conv.CONV_RULE`](#Conv.CONV_RULE),
[`Tactic.CONV_TAC`](#Tactic.CONV_TAC),
[`Conv.RIGHT_CONV_RULE`](#Conv.RIGHT_CONV_RULE)
