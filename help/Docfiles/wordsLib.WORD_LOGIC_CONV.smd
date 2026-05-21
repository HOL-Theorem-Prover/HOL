## `WORD_LOGIC_CONV`

``` hol4
wordsLib.WORD_LOGIC_CONV : conv
```

------------------------------------------------------------------------

Conversion based on `WORD_LOGIC_ss`.

The conversion `WORD_LOGIC_CONV` converts word logic expressions into a
canonical form.

### Example

``` hol4
- WORD_LOGIC_CONV “a && (b !! ~a !! c)”
<<HOL message: inventing new type variable names: 'a>>
> val it = |- a && (b !! ~a !! c) = a && b !! a && c : thm
```

### See also

[`wordsLib.WORD_LOGIC_ss`](#wordsLib.WORD_LOGIC_ss),
[`wordsLib.WORD_ARITH_CONV`](#wordsLib.WORD_ARITH_CONV),
[`wordsLib.WORD_MUL_LSL_CONV`](#wordsLib.WORD_MUL_LSL_CONV),
[`wordsLib.WORD_CONV`](#wordsLib.WORD_CONV),
[`wordsLib.WORD_BIT_EQ_CONV`](#wordsLib.WORD_BIT_EQ_CONV),
[`wordsLib.WORD_EVAL_CONV`](#wordsLib.WORD_EVAL_CONV)
