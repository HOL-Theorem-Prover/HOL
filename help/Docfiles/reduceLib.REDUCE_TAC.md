## `REDUCE_TAC`

``` hol4
reduceLib.REDUCE_TAC : tactic
```

------------------------------------------------------------------------

Performs arithmetic or boolean reduction on a goal at all levels
possible.

`REDUCE_TAC` attempts to transform a goal by applying `REDUCE_CONV`. It
will prove any true goal which is constructed from numerals and the
boolean constants `T` and `F`.

### Failure

Never fails, but may not advance the goal.

### Example

The following example takes a couple of minutes' CPU time:

``` hol4
   > g ‘((1 EXP 3) + (12 EXP 3) = 1729) /\ ((9 EXP 3) + (10 EXP 3) = 1729)’;

   > e reduceLib.REDUCE_TAC;;
   OK..
   val it = 
      Initial goal proved
      ⊢ 1 EXP 3 + 12 EXP 3 = 1729 ∧ 9 EXP 3 + 10 EXP 3 = 1729 : proof
```

### See also

[`reduceLib.RED_CONV`](#reduceLib.RED_CONV),
[`reduceLib.REDUCE_CONV`](#reduceLib.REDUCE_CONV),
[`reduceLib.REDUCE_RULE`](#reduceLib.REDUCE_RULE)
