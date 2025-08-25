## `RESTR_EVAL_RULE`

``` hol4
computeLib.RESTR_EVAL_RULE : term list -> thm -> thm
```

------------------------------------------------------------------------

Symbolically evaluate a theorem, except for specified constants.

This is a version of `RESTR_EVAL_CONV` that works on theorems.

### Failure

As for `RESTR_EVAL_CONV`.

Controlling symbolic evaluation when it loops or becomes exponential.

### See also

[`bossLib.EVAL`](#bossLib.EVAL),
[`bossLib.EVAL_RULE`](#bossLib.EVAL_RULE),
[`computeLib.RESTR_EVAL_CONV`](#computeLib.RESTR_EVAL_CONV),
[`computeLib.RESTR_EVAL_TAC`](#computeLib.RESTR_EVAL_TAC)
