## `EVAL`

``` hol4
bossLib.EVAL : conv
```

------------------------------------------------------------------------

Evaluate a term by deduction.

An invocation `EVAL M` symbolically evaluates `M` by applying the
defining equations of constants occurring in `M`. These equations are
held in a mutable datastructure that is automatically added to by
`Hol_datatype`, `Define`, and `tprove`. The underlying algorithm is
call-by-value with a few differences, see the entry for `CBV_CONV` for
details.

### Failure

Never fails, but may diverge.

### Example

``` hol4
- EVAL (Term `REVERSE (MAP (\x. x + a) [x;y;z])`);
> val it = |- REVERSE (MAP (\x. x + a) [x; y; z]) = [z + a; y + a; x + a]
   : thm
```

### Comments

In order for recursive functions over numbers to be applied by `EVAL`,
pattern matching over `SUC` and `0` needs to be replaced by destructors.
For example, the equations for `FACT` would have to be rephrased as
`FACT n = if n = 0 then 1 else n * FACT (n-1)`.

### See also

[`computeLib.CBV_CONV`](#computeLib.CBV_CONV),
[`computeLib.RESTR_EVAL_CONV`](#computeLib.RESTR_EVAL_CONV),
[`bossLib.EVAL_TAC`](#bossLib.EVAL_TAC),
[`computeLib.monitoring`](#computeLib.monitoring),
[`bossLib.Define`](#bossLib.Define)
