## `WORD_CONV`

``` hol4
wordsLib.WORD_CONV : conv
```

------------------------------------------------------------------------

Conversion for words.

The conversion `WORD_CONV` applies the simpset fragment `WORD_ss`.

### Example

``` hol4
- WORD_CONV “c * (a + b) !! (b + a) * c”
<<HOL message: inventing new type variable names: 'a>>
> val it = |- c * (a + b) !! (b + a) * c = a * c + b * c : thm
```

### See also

[`wordsLib.WORD_ss`](#wordsLib.WORD_ss),
[`wordsLib.WORD_ARITH_CONV`](#wordsLib.WORD_ARITH_CONV),
[`wordsLib.WORD_LOGIC_CONV`](#wordsLib.WORD_LOGIC_CONV),
[`wordsLib.WORD_MUL_LSL_CONV`](#wordsLib.WORD_MUL_LSL_CONV),
[`wordsLib.WORD_BIT_EQ_CONV`](#wordsLib.WORD_BIT_EQ_CONV),
[`wordsLib.WORD_EVAL_CONV`](#wordsLib.WORD_EVAL_CONV)
