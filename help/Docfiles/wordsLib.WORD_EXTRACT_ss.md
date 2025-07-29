## `WORD_EXTRACT_ss`

``` hol4
wordsLib.WORD_EXTRACT_ss : ssfrag
```

------------------------------------------------------------------------

Simplification fragment for words.

The fragment `WORD_EXTRACT_ss` simplifies the operations `w2w`, `sw2sw`
(signed word-to-word conversion), `word_lsb`, `word_msb`, `word_bit`,
`>>` (arithmetic right shift), `>>>` (logical right shift), `#>>`
(rotate right), `#<<` (rotate left), `@@` (concatenation), `--` (word
bits) and `''` (word slice). The result is expressed in terms of `!!`
(disjunction), `<<` (left shift) and `><` (word extract).

### Example

``` hol4
- SIMP_CONV (std_ss++WORD_ss++WORD_EXTRACT_ss) [] “(((7 >< 5) (a:word8)):3 word @@ ((4 >< 0) a):5 word) : word8”
> val it = |- (7 >< 5) a @@ (4 >< 0) a = a : thm

- SIMP_CONV (std_ss++WORD_ss++WORD_EXTRACT_ss) [] “(4 -- 2) ((a:word8) #>> 4)”
> val it = |- (4 -- 2) (a #>> 4) = (7 >< 6) a !! (0 >< 0) a << 2 : thm

- SIMP_CONV (std_ss++WORD_ss++WORD_EXTRACT_ss) [] “w2w (sw2sw (a:word4):word8):word4”
> val it = |- w2w (sw2sw a) = a : thm
```

### Comments

Best used in combination with `WORD_ss`.

### See also

[`fcpLib.FCP_ss`](#fcpLib.FCP_ss),
[`wordsLib.BIT_ss`](#wordsLib.BIT_ss),
[`wordsLib.SIZES_ss`](#wordsLib.SIZES_ss),
[`wordsLib.WORD_ARITH_ss`](#wordsLib.WORD_ARITH_ss),
[`wordsLib.WORD_LOGIC_ss`](#wordsLib.WORD_LOGIC_ss),
[`wordsLib.WORD_ARITH_EQ_ss`](#wordsLib.WORD_ARITH_EQ_ss),
[`wordsLib.WORD_BIT_EQ_ss`](#wordsLib.WORD_BIT_EQ_ss),
[`wordsLib.WORD_SHIFT_ss`](#wordsLib.WORD_SHIFT_ss),
[`wordsLib.WORD_MUL_LSL_ss`](#wordsLib.WORD_MUL_LSL_ss),
[`wordsLib.WORD_ss`](#wordsLib.WORD_ss)
