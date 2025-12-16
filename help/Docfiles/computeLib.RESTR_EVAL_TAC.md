## `RESTR_EVAL_TAC`

``` hol4
computeLib.RESTR_EVAL_TAC : term list -> tactic
```

------------------------------------------------------------------------

Symbolically evaluate a theorem, except for specified constants.

This is a tactic version of `RESTR_EVAL_CONV`.

### Failure

As for `RESTR_EVAL_CONV`.

Controlling symbolic evaluation when it loops or becomes exponential.

### See also

[`bossLib.EVAL`](#bossLib.EVAL),
[`bossLib.EVAL_RULE`](#bossLib.EVAL_RULE),
[`bossLib.EVAL_TAC`](#bossLib.EVAL_TAC),
[`computeLib.RESTR_EVAL_CONV`](#computeLib.RESTR_EVAL_CONV),
[`computeLib.RESTR_EVAL_RULE`](#computeLib.RESTR_EVAL_RULE)
