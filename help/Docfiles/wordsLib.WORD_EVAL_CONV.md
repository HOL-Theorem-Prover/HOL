## `WORD_EVAL_CONV`

``` hol4
wordsLib.WORD_EVAL_CONV : conv
```

------------------------------------------------------------------------

Evaluation for words.

The conversion `WORD_EVAL_CONV` provides efficient evaluation for word
operations. It uses `wordsLib.words_compset`.

### Example

``` hol4
- WORD_EVAL_CONV “word_log2 (word_reverse (3w * (33w #<< 4))) : word32”
> val it = |- word_log2 (word_reverse (3w * 33w #<< 4)) = 27w : thm
```

### Comments

This conversion is best suited to evaluating ground terms with known
word lengths. The conversion `wordsLib.WORD_CONV` is a suitable
alternative.

### See also

[`bossLib.EVAL`](#bossLib.EVAL),
[`computeLib.CBV_CONV`](#computeLib.CBV_CONV),
[`wordsLib.WORD_LOGIC_CONV`](#wordsLib.WORD_LOGIC_CONV),
[`wordsLib.WORD_MUL_LSL_CONV`](#wordsLib.WORD_MUL_LSL_CONV),
[`wordsLib.WORD_CONV`](#wordsLib.WORD_CONV),
[`wordsLib.WORD_BIT_EQ_CONV`](#wordsLib.WORD_BIT_EQ_CONV),
[`wordsLib.WORD_EVAL_CONV`](#wordsLib.WORD_EVAL_CONV)
