## `WORD_LOGIC_ss`

``` hol4
wordsLib.WORD_LOGIC_ss : ssfrag
```

------------------------------------------------------------------------

Simplification fragment for words.

The fragment `WORD_LOGIC_ss` does AC simplification for word
conjunction, disjunction and 1's complement (negation). If the word
length is known then further simplification occurs, in particular for
`~(n2w n)`.

### Example

``` hol4
- SIMP_CONV (pure_ss++WORD_LOGIC_ss) [] “3w !! 12w && a !! ~4w !! a && 16w”
<<HOL message: inventing new type variable names: 'a>>
> val it = |- 3w !! 12w && a !! ~4w !! a && 16w = 28w && a !! $- 5w : thm
```

More simplification occurs when the word length is known.

``` hol4
- SIMP_CONV (pure_ss++WORD_LOGIC_ss) [] “~12w !! ~14w : word8”
> val it = |- ~12w !! ~14w = 243w : thm
```

### Comments

The term `$- 1w` represents `UINT_MAXw`, which is the supremum in
bitwise operations.

### See also

[`wordsLib.WORD_LOGIC_CONV`](#wordsLib.WORD_LOGIC_CONV),
[`wordsLib.WORD_CONV`](#wordsLib.WORD_CONV),
[`fcpLib.FCP_ss`](#fcpLib.FCP_ss),
[`wordsLib.BIT_ss`](#wordsLib.BIT_ss),
[`wordsLib.SIZES_ss`](#wordsLib.SIZES_ss),
[`wordsLib.WORD_ARITH_ss`](#wordsLib.WORD_ARITH_ss),
[`wordsLib.WORD_SHIFT_ss`](#wordsLib.WORD_SHIFT_ss),
[`wordsLib.WORD_ARITH_EQ_ss`](#wordsLib.WORD_ARITH_EQ_ss),
[`wordsLib.WORD_BIT_EQ_ss`](#wordsLib.WORD_BIT_EQ_ss),
[`wordsLib.WORD_EXTRACT_ss`](#wordsLib.WORD_EXTRACT_ss),
[`wordsLib.WORD_MUL_LSL_ss`](#wordsLib.WORD_MUL_LSL_ss),
[`wordsLib.WORD_ss`](#wordsLib.WORD_ss)
