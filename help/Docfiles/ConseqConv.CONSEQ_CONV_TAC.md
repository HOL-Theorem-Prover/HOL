## `CONSEQ_CONV_TAC`

``` hol4
ConseqConv.CONSEQ_CONV_TAC : directed_conseq_conv -> tactic
```

------------------------------------------------------------------------

Reduces the goal using a consequence conversion.

`CONSEQ_CONV_TAC c` tries to strengthen a goal `P` using `c` to a new
goal `P'`. It then remains to show that `P'` holds.

### See also

[`Tactic.MATCH_MP_TAC`](#Tactic.MATCH_MP_TAC)
