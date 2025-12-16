## `REDUCE_CONV`

``` hol4
reduceLib.REDUCE_CONV : conv
```

------------------------------------------------------------------------

Performs arithmetic or boolean reduction at all levels possible.

The conversion `REDUCE_CONV` attempts to apply, in bottom-up order to
all suitable redexes, arithmetic computation conversions for all of the
standard operators from `arithmeticTheory`. The conversions are
implemented as rewrites applied by `CBV_CONV`. In particular, it is
designed to prove the appropriate reduction for an arbitrarily
complicated expression constructed from numerals, those operators, and
the boolean constants `T` and `F`, and will do this to all such
sub-expressions within a term.

### Failure

Never fails, but may give a reflexive equation.

### Example

``` hol4
> reduceLib.REDUCE_CONV “(2=3) = F”;
val it = ⊢ (2 = 3 ⇔ F) ⇔ T : thm

> reduceLib.REDUCE_CONV “if 100 < 200 then 2 EXP (8 DIV 2)
                         else 3 EXP ((26 EXP 0) * 3)”;
val it = ⊢ (if 100 < 200 then 2 ** (8 DIV 2)
            else 3 ** (26 ** 0 * 3)) =
           16: thm

> reduceLib.REDUCE_CONV “(15 = 16) \/ (15 < 16)”;
val it = ⊢ 15 = 16 ∨ 15 < 16 ⇔ T: thm

> reduceLib.REDUCE_CONV “1 + x”;
val it = ⊢ 1 + x = 1 + x: thm

> reduceLib.REDUCE_CONV “!x:num. x = x”;
val it = ⊢ (∀x. x = x) ⇔ ∀x. T: thm
```

### Comments

This entry-point is also available as `numLib.REDUCE_CONV`.

### See also

[`computeLib.CBV_CONV`](#computeLib.CBV_CONV),
[`reduceLib.RED_CONV`](#reduceLib.RED_CONV),
[`reduceLib.REDUCE_RULE`](#reduceLib.REDUCE_RULE),
[`reduceLib.REDUCE_TAC`](#reduceLib.REDUCE_TAC)
