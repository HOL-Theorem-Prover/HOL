## `WORD_BIT_EQ_CONV`

``` hol4
wordsLib.WORD_BIT_EQ_CONV : conv
```

------------------------------------------------------------------------

Conversion based on `WORD_BIT_EQ_ss`.

The conversion `WORD_BIT_EQ_CONV` performs simplification using
`fcpLib.FCP_ss`.

### Example

``` hol4
- WORD_BIT_EQ_CONV “a << 2 >>> 1 = ((5 -- 0) a << 1) :word8”
> val it = |- (a << 2 >>> 1 = (5 -- 0) a << 1) = T : thm
```

### See also

[`wordsLib.WORD_BIT_EQ_ss`](#wordsLib.WORD_BIT_EQ_ss),
[`blastLib.BBLAST_CONV`](#blastLib.BBLAST_CONV),
[`wordsLib.WORD_ARITH_CONV`](#wordsLib.WORD_ARITH_CONV),
[`wordsLib.WORD_LOGIC_CONV`](#wordsLib.WORD_LOGIC_CONV),
[`wordsLib.WORD_MUL_LSL_CONV`](#wordsLib.WORD_MUL_LSL_CONV),
[`wordsLib.WORD_CONV`](#wordsLib.WORD_CONV),
[`wordsLib.WORD_EVAL_CONV`](#wordsLib.WORD_EVAL_CONV)
