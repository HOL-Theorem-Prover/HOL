## `EVALn`

``` hol4
bossLib.EVALn : int -> conv
```

------------------------------------------------------------------------

Evaluate a term by deduction, limiting number of steps taken.

An invocation `EVALn n M` symbolically evaluates `M` by applying the
defining equations of constants occurring in `M`, stopping when `M`
reduces to a normal form, or after `n` reduction steps have occurred. If
`n` is large enough and there is a normal form, the behaviour will be
the same as `EVAL M`, which see.

### Failure

Never fails.

### Example

In the example below, a custom pretty-printer hides a potentially large
term involving the terms that are used to represent intermediates stages
of numeral computation.

``` hol4
   - EVALn 50 “MAP (\x. x * x) [1;2;3;4;5]”;
   val it =
      ⊢ MAP (λx. x²) [1; 2; 3; 4; 5] =
        1::4:: <..num comp'n..> ::MAP (λx. x²) [4; 5]: thm
```

### See also

[`computeLib.CBV_CONV`](#computeLib.CBV_CONV),
[`computeLib.RESTR_EVAL_CONV`](#computeLib.RESTR_EVAL_CONV),
[`bossLib.EVAL_TAC`](#bossLib.EVAL_TAC),
[`computeLib.monitoring`](#computeLib.monitoring),
[`bossLib.Define`](#bossLib.Define)
