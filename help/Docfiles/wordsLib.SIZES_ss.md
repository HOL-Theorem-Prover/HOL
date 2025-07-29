## `SIZES_ss`

``` hol4
wordsLib.SIZES_ss : ssfrag
```

------------------------------------------------------------------------

Simplification fragment for words.

The fragment `SIZES_ss` evaluates terms `“dimindex(:'a)”`,
`“dimword(:'a)”`, `“INT_MIN(:'a)”`, and `“FINITE (UNIV : 'a set)”` for
numeric types.

### Example

``` hol4
- SIMP_CONV (pure_ss++SIZES_ss) [] “dimindex(:32) + INT_MIN(:32) + dimword(:32)”
> val it =
    |- dimindex (:32) + INT_MIN (:32) + dimword (:32) =
       32 + 2147483648 + 4294967296 : thm
```

### See also

[`wordsLib.SIZES_CONV`](#wordsLib.SIZES_CONV),
[`wordsLib.WORD_CONV`](#wordsLib.WORD_CONV),
[`fcpLib.FCP_ss`](#fcpLib.FCP_ss),
[`wordsLib.BIT_ss`](#wordsLib.BIT_ss),
[`wordsLib.WORD_ARITH_ss`](#wordsLib.WORD_ARITH_ss),
[`wordsLib.WORD_LOGIC_ss`](#wordsLib.WORD_LOGIC_ss),
[`wordsLib.WORD_SHIFT_ss`](#wordsLib.WORD_SHIFT_ss),
[`wordsLib.WORD_ARITH_EQ_ss`](#wordsLib.WORD_ARITH_EQ_ss),
[`wordsLib.WORD_BIT_EQ_ss`](#wordsLib.WORD_BIT_EQ_ss),
[`wordsLib.WORD_EXTRACT_ss`](#wordsLib.WORD_EXTRACT_ss),
[`wordsLib.WORD_MUL_LSL_ss`](#wordsLib.WORD_MUL_LSL_ss),
[`wordsLib.WORD_ss`](#wordsLib.WORD_ss)
