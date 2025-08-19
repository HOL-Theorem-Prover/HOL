## `AP_THM`

``` hol4
Thm.AP_THM : thm -> term -> thm
```

------------------------------------------------------------------------

Proves equality of equal functions applied to a term.

When applied to a theorem `A |- f = g` and a term `x`, the inference
rule `AP_THM` returns the theorem `A |- f x = g x`.

``` hol4
      A |- f = g
   ----------------  AP_THM (A |- f = g) x
    A |- f x = g x
```

### Failure

Fails unless the conclusion of the theorem is an equation, both sides of
which are functions whose domain type is the same as that of the
supplied term.

### See also

[`Tactic.AP_THM_TAC`](#Tactic.AP_THM_TAC),
[`Thm.AP_TERM`](#Thm.AP_TERM), [`Drule.ETA_CONV`](#Drule.ETA_CONV),
[`Drule.EXT`](#Drule.EXT), [`Conv.FUN_EQ_CONV`](#Conv.FUN_EQ_CONV),
[`Thm.MK_COMB`](#Thm.MK_COMB)
