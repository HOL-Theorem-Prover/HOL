## `AP_TERM`

``` hol4
Thm.AP_TERM : term -> thm -> thm
```

------------------------------------------------------------------------

Applies a function to both sides of an equational theorem.

When applied to a term `f` and a theorem `A |- x = y`, the inference
rule `AP_TERM` returns the theorem `A |- f x = f y`.

``` hol4
      A |- x = y
   ----------------  AP_TERM f
    A |- f x = f y
```

### Failure

Fails unless the theorem is equational and the supplied term is a
function whose domain type is the same as the type of both sides of the
equation.

### See also

[`Tactic.AP_TERM_TAC`](#Tactic.AP_TERM_TAC),
[`Thm.AP_THM`](#Thm.AP_THM), [`Tactic.AP_THM_TAC`](#Tactic.AP_THM_TAC),
[`Thm.MK_COMB`](#Thm.MK_COMB)
