## `WORD_ARITH_ss`

``` hol4
wordsLib.WORD_ARITH_ss : ssfrag
```

------------------------------------------------------------------------

Simplification fragment for words.

The fragment `WORD_ARITH_ss` does AC simplification for word
multiplication, addition and subtraction. It also simplifies `INT_MINw`,
`INT_MAXw` and `UINT_MAXw`. If the word length is known then further
simplification may occur, in particular for `$- (n2w n)` and
`w2n (n2w n)`.

### Example

``` hol4
- SIMP_CONV (pure_ss++WORD_ARITH_ss) [] “3w * b + a + 2w * b - a * 4w”
<<HOL message: inventing new type variable names: 'a>>
> val it = |- 3w * b + a + 2w * b - a * 4w = $- 3w * a + 5w * b : thm

- SIMP_CONV (pure_ss++WORD_ARITH_ss) [] “INT_MINw + INT_MAXw + UINT_MAXw”
<<HOL message: inventing new type variable names: 'a>>
> val it = |- INT_MINw + INT_MAXw + UINT_MAXw = $- 2w : thm
```

More simplification occurs when the word length is known.

``` hol4
- SIMP_CONV (pure_ss++WORD_ARITH_ss) [] “3w * b + a + 2w * b - a * 4w:word2”
> val it = |- 3w * b + a + 2w * b - a * 4w = a + b : thm

- SIMP_CONV (pure_ss++WORD_ARITH_ss) [] “w2n (33w:word4)”;
> val it = |- w2n 33w = 1 : thm
```

### Comments

Any term of value `UINT_MAXw` simplifies to `$- 1w` even when the word
length is known - this helps when simplifying bitwise operations. If the
word length is not known then `INT_MAXw` becomes `INT_MINw + $- 1w`.

### See also

[`wordsLib.WORD_ARITH_CONV`](#wordsLib.WORD_ARITH_CONV),
[`wordsLib.WORD_CONV`](#wordsLib.WORD_CONV),
[`fcpLib.FCP_ss`](#fcpLib.FCP_ss),
[`wordsLib.BIT_ss`](#wordsLib.BIT_ss),
[`wordsLib.SIZES_ss`](#wordsLib.SIZES_ss),
[`wordsLib.WORD_LOGIC_ss`](#wordsLib.WORD_LOGIC_ss),
[`wordsLib.WORD_SHIFT_ss`](#wordsLib.WORD_SHIFT_ss),
[`wordsLib.WORD_ARITH_EQ_ss`](#wordsLib.WORD_ARITH_EQ_ss),
[`wordsLib.WORD_BIT_EQ_ss`](#wordsLib.WORD_BIT_EQ_ss),
[`wordsLib.WORD_EXTRACT_ss`](#wordsLib.WORD_EXTRACT_ss),
[`wordsLib.WORD_MUL_LSL_ss`](#wordsLib.WORD_MUL_LSL_ss),
[`wordsLib.WORD_ss`](#wordsLib.WORD_ss)
