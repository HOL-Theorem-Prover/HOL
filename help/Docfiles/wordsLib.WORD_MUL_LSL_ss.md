## `WORD_MUL_LSL_ss`

``` hol4
wordsLib.WORD_MUL_LSL_ss : ssfrag
```

------------------------------------------------------------------------

Simplification fragment for words.

The fragment `WORD_MUL_LSL_ss` simplifies a multiplication by a word
literal into a sum of left shifts.

### Example

``` hol4
- SIMP_CONV (std_ss++WORD_MUL_LSL_ss) [] “49w * a”
> val it = |- 49w * a = a << 5 + a << 4 + a : thm

- SIMP_CONV (std_ss++WORD_ss++WORD_MUL_LSL_ss) [] “2w * a + a << 1”
<<HOL message: inventing new type variable names: 'a>>
> val it = |- 2w * a + a << 1 = a << 2 : thm
```

### Comments

This fragment is not included in `WORDS_ss`. It should not be used in
combination with `WORD_ARITH_EQ_ss` or `wordsLib.WORD_ARITH_CONV`, since
these convert left shifts into multiplications.

### See also

[`wordsLib.WORD_MUL_LSL_CONV`](#wordsLib.WORD_MUL_LSL_CONV),
[`fcpLib.FCP_ss`](#fcpLib.FCP_ss),
[`wordsLib.BIT_ss`](#wordsLib.BIT_ss),
[`wordsLib.SIZES_ss`](#wordsLib.SIZES_ss),
[`wordsLib.WORD_ARITH_ss`](#wordsLib.WORD_ARITH_ss),
[`wordsLib.WORD_LOGIC_ss`](#wordsLib.WORD_LOGIC_ss),
[`wordsLib.WORD_ARITH_EQ_ss`](#wordsLib.WORD_ARITH_EQ_ss),
[`wordsLib.WORD_BIT_EQ_ss`](#wordsLib.WORD_BIT_EQ_ss),
[`wordsLib.WORD_SHIFT_ss`](#wordsLib.WORD_SHIFT_ss),
[`wordsLib.WORD_EXTRACT_ss`](#wordsLib.WORD_EXTRACT_ss),
[`wordsLib.WORD_ss`](#wordsLib.WORD_ss)
