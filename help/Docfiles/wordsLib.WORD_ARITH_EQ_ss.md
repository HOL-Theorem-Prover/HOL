## `WORD_ARITH_EQ_ss`

``` hol4
wordsLib.WORD_ARITH_EQ_ss : ssfrag
```

------------------------------------------------------------------------

Simplification fragment for words.

The fragment `WORD_ARITH_EQ_ss` simplifies `“a = b : 'a word”` to
`“a - b = 0w”`. It also simplifies using the theorems
`WORD_LEFT_ADD_DISTRIB`, `WORD_RIGHT_ADD_DISTRIB`, `WORD_MUL_LSL` and
`WORD_NOT`. When combined with `wordsLib.WORD_ARITH_ss` this fragment
can be used to test for the arithmetic equality of words.

### Example

``` hol4
- SIMP_CONV (pure_ss++WORD_ARITH_ss++WORD_ARITH_EQ_ss) [] “3w * (a + b) = b + 3w * a”
<<HOL message: inventing new type variable names: 'a>>
> val it = |- (3w * (a + b) = b + 3w * a) = (2w * b = 0w) : thm
```

### Comments

This fragment is not included in `WORDS_ss`.

### See also

[`wordsLib.WORD_ARITH_CONV`](#wordsLib.WORD_ARITH_CONV),
[`fcpLib.FCP_ss`](#fcpLib.FCP_ss),
[`wordsLib.BIT_ss`](#wordsLib.BIT_ss),
[`wordsLib.SIZES_ss`](#wordsLib.SIZES_ss),
[`wordsLib.WORD_ARITH_ss`](#wordsLib.WORD_ARITH_ss),
[`wordsLib.WORD_LOGIC_ss`](#wordsLib.WORD_LOGIC_ss),
[`wordsLib.WORD_SHIFT_ss`](#wordsLib.WORD_SHIFT_ss),
[`wordsLib.WORD_BIT_EQ_ss`](#wordsLib.WORD_BIT_EQ_ss),
[`wordsLib.WORD_EXTRACT_ss`](#wordsLib.WORD_EXTRACT_ss),
[`wordsLib.WORD_MUL_LSL_ss`](#wordsLib.WORD_MUL_LSL_ss),
[`wordsLib.WORD_ss`](#wordsLib.WORD_ss)
