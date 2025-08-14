## `WORD_SHIFT_ss`

``` hol4
wordsLib.WORD_SHIFT_ss : ssfrag
```

------------------------------------------------------------------------

Simplification fragment for words.

The fragment `WORD_SHIFT_ss` does some basic simplifications for the
operations: `<<` (left shift), `>>` (arithmetic right shift), `>>>`
(logical right shift), `#>>` (rotate right) and `#<<` (rotate left).
More simplification is possible when used in combination with
`wordsLib.SIZES_ss`.

### Example

``` hol4
- SIMP_CONV (std_ss++WORD_SHIFT_ss) [] “a << 2 << 3 + a >> 3 >> 2 + a >>> 1 >>> 2 + a #<< 1 #<< 2”
<<HOL message: inventing new type variable names: 'a>>
> val it =
    |- a << 2 << 3 + a >> 3 >> 2 + a >>> 1 >>> 2 + a #<< 1 #<< 2 =
       a << 5 + a >> 5 + a >>> 3 + a #<< 3 : thm

- SIMP_CONV (std_ss++WORD_SHIFT_ss) [] “a >> 0 + 0w << n + a #<< 2 #>> 2”
<<HOL message: inventing new type variable names: 'a>>
> val it = |- a >> 0 + 0w << n + a #<< 2 #>> 2 = a + 0w + a : thm
```

More simplification is possible when the word length is known.

``` hol4
- SIMP_CONV (std_ss++SIZES_ss++WORD_SHIFT_ss) [] “a << 4 + (a #<< 6) : word4”
> val it = |- a << 4 = 0w + a #<< 2 : thm
```

### Comments

When the word length is known the fragment `WORD_ss` simplifies `#<<` to
`#>>`.

### See also

[`fcpLib.FCP_ss`](#fcpLib.FCP_ss),
[`wordsLib.BIT_ss`](#wordsLib.BIT_ss),
[`wordsLib.SIZES_ss`](#wordsLib.SIZES_ss),
[`wordsLib.WORD_ARITH_ss`](#wordsLib.WORD_ARITH_ss),
[`wordsLib.WORD_LOGIC_ss`](#wordsLib.WORD_LOGIC_ss),
[`wordsLib.WORD_ARITH_EQ_ss`](#wordsLib.WORD_ARITH_EQ_ss),
[`wordsLib.WORD_BIT_EQ_ss`](#wordsLib.WORD_BIT_EQ_ss),
[`wordsLib.WORD_EXTRACT_ss`](#wordsLib.WORD_EXTRACT_ss),
[`wordsLib.WORD_MUL_LSL_ss`](#wordsLib.WORD_MUL_LSL_ss),
[`wordsLib.WORD_ss`](#wordsLib.WORD_ss)
