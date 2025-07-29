## `BIT_ss`

``` hol4
wordsLib.BIT_ss : ssfrag
```

------------------------------------------------------------------------

Simplification fragment for words.

The fragment `BIT_ss` rewrites the term `“BIT i n”` for ground `n`.

### Example

``` hol4
- SIMP_CONV (std_ss++BIT_ss) [] “BIT i 33”;
> val it = |- BIT i 33 = i IN {0; 5} : thm

- SIMP_CONV (std_ss++BIT_ss) [] “BIT 5 33”;
> val it = |- BIT 5 33 = T : thm
```

### See also

[`wordsLib.WORD_CONV`](#wordsLib.WORD_CONV),
[`fcpLib.FCP_ss`](#fcpLib.FCP_ss),
[`wordsLib.SIZES_ss`](#wordsLib.SIZES_ss),
[`wordsLib.WORD_ARITH_ss`](#wordsLib.WORD_ARITH_ss),
[`wordsLib.WORD_LOGIC_ss`](#wordsLib.WORD_LOGIC_ss),
[`wordsLib.WORD_SHIFT_ss`](#wordsLib.WORD_SHIFT_ss),
[`wordsLib.WORD_ARITH_EQ_ss`](#wordsLib.WORD_ARITH_EQ_ss),
[`wordsLib.WORD_BIT_EQ_ss`](#wordsLib.WORD_BIT_EQ_ss),
[`wordsLib.WORD_EXTRACT_ss`](#wordsLib.WORD_EXTRACT_ss),
[`wordsLib.WORD_MUL_LSL_ss`](#wordsLib.WORD_MUL_LSL_ss),
[`wordsLib.WORD_ss`](#wordsLib.WORD_ss)
