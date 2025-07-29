## `WORD_MUL_LSL_CONV`

``` hol4
wordsLib.WORD_MUL_LSL_CONV : conv
```

------------------------------------------------------------------------

Conversion based on `WORD_MUL_LSL_ss`.

The conversion `WORD_MUL_LSL_CONV` converts a multiplication by a word
literal into a sum of left shifts.

### Example

``` hol4
- WORD_MUL_LSL_CONV “49w * a”
> val it = |- 49w * a = a << 5 + a << 4 + a : thm
```

### See also

[`wordsLib.WORD_MUL_LSL_ss`](#wordsLib.WORD_MUL_LSL_ss),
[`wordsLib.WORD_DIV_LSR_CONV`](#wordsLib.WORD_DIV_LSR_CONV),
[`wordsLib.WORD_ARITH_CONV`](#wordsLib.WORD_ARITH_CONV),
[`wordsLib.WORD_LOGIC_CONV`](#wordsLib.WORD_LOGIC_CONV),
[`wordsLib.WORD_CONV`](#wordsLib.WORD_CONV),
[`wordsLib.WORD_BIT_EQ_CONV`](#wordsLib.WORD_BIT_EQ_CONV),
[`wordsLib.WORD_EVAL_CONV`](#wordsLib.WORD_EVAL_CONV)
