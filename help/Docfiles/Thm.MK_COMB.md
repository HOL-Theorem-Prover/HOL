## `MK_COMB`

``` hol4
Thm.MK_COMB : thm * thm -> thm
```

------------------------------------------------------------------------

Proves equality of combinations constructed from equal functions and
operands.

When applied to theorems `A1 |- f = g` and `A2 |- x = y`, the inference
rule `MK_COMB` returns the theorem `A1 u A2 |- f x = g y`.

``` hol4
    A1 |- f = g   A2 |- x = y
   ---------------------------  MK_COMB
       A1 u A2 |- f x = g y
```

### Failure

Fails unless both theorems are equational and `f` and `g` are functions
whose domain types are the same as the types of `x` and `y`
respectively.

### See also

[`Thm.AP_TERM`](#Thm.AP_TERM), [`Thm.AP_THM`](#Thm.AP_THM),
[`Tactic.MK_COMB_TAC`](#Tactic.MK_COMB_TAC)
