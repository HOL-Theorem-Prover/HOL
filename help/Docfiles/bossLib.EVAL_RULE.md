## `EVAL_RULE`

``` hol4
bossLib.EVAL_RULE : thm -> thm
```

------------------------------------------------------------------------

Evaluate conclusion of a theorem.

An invocation `EVAL_RULE th` symbolically evaluates the conclusion of
`th` by applying the defining equations of constants which occur in the
conclusion of `th`. These equations are held in a mutable datastructure
that is automatically added to by `Hol_datatype`, `Define`, and
`tprove`. The underlying algorithm is call-by-value with a few
differences, see the entry for `CBV_CONV` for details.

### Failure

Never fails, but may diverge.

### Example

``` hol4
- val th = ASSUME(Term `x = MAP FACT (REVERSE [1;2;3;4;5;6;7;8;9;10])`);
> val th =  [.] |- x = MAP FACT (REVERSE [1; 2; 3; 4; 5; 6; 7; 8; 9; 10])

- EVAL_RULE th;
> val it =  [.] |- x = [3628800; 362880; 40320; 5040; 720; 120; 24; 6; 2; 1]

- hyp it;
> val it = [`x = MAP FACT (REVERSE [1; 2; 3; 4; 5; 6; 7; 8; 9; 10])`]
```

### Comments

In order for recursive functions over numbers to be applied by
`EVAL_RULE`, pattern matching over `SUC` and `0` needs to be replaced by
destructors. For example, the equations for `FACT` would have to be
rephrased as `FACT n = if n = 0 then 1 else n * FACT (n-1)`.

### See also

[`bossLib.EVAL`](#bossLib.EVAL),
[`bossLib.EVAL_TAC`](#bossLib.EVAL_TAC),
[`computeLib.CBV_CONV`](#computeLib.CBV_CONV)
