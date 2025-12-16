## `CONV_RULE`

``` hol4
Conv.CONV_RULE : (conv -> thm -> thm)
```

------------------------------------------------------------------------

Makes an inference rule from a conversion.

If `c` is a conversion, then `CONV_RULE c` is an inference rule that
applies `c` to the conclusion of a theorem. That is, if `c` maps a term
`"t"` to the theorem `|- t = t'`, then the rule `CONV_RULE c` infers
`|- t'` from the theorem `|- t`. More precisely, if `c "t"` returns
`A' |- t = t'`, then:

``` hol4
       A |- t
   --------------  CONV_RULE c
    A u A' |- t'
```

Note that if the conversion `c` returns a theorem with assumptions, then
the resulting inference rule adds these to the assumptions of the
theorem it returns.

If `c` raises `UNCHANGED` then `CONV_RULE c th` returns `th`.

### Failure

`CONV_RULE c th` fails if `c` fails (other than by raising `UNCHANGED`)
when applied to the conclusion of `th`. The function returned by
`CONV_RULE c` will also fail if the ML function `c:term->thm` is not, in
fact, a conversion (i.e. a function that maps a term `t` to a theorem
`|- t = t'`).

### See also

[`Abbrev.conv`](#Abbrev.conv), [`Conv.UNCHANGED`](#Conv.UNCHANGED),
[`Tactic.CONV_TAC`](#Tactic.CONV_TAC),
[`Conv.HYP_CONV_RULE`](#Conv.HYP_CONV_RULE),
[`Conv.RIGHT_CONV_RULE`](#Conv.RIGHT_CONV_RULE)
