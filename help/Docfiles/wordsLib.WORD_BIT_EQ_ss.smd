## `WORD_BIT_EQ_ss`

``` hol4
wordsLib.WORD_BIT_EQ_ss : ssfrag
```

------------------------------------------------------------------------

Simplification fragment for words.

The fragment `WORD_BIT_EQ_ss` simplifies using `fcpLib.FCP_ss` and the
definitions of "bitwise" operations, e.g., conjunction, disjunction, 1's
complement, shifts, concatenation and sub-word extraction. Can be used
in combination with decision procedures to test for the bitwise equality
of words.

### Example

``` hol4
- SIMP_CONV (std_ss++WORD_BIT_EQ_ss) [] “a = b : 'a word”
> val it = |- (a = b) = !i. i < dimindex (:'a) ==> (a ' i = b ' i) : thm
```

Further simplification occurs when the word length is known.

``` hol4
- SIMP_CONV (std_ss++WORD_BIT_EQ_ss) [] “a = b : word2”
> val it = |- (a = b) = (a ' 1 = b ' 1) /\ (a ' 0 = b ' 0) : thm
```

Best used in combination with decision procedures.

``` hol4
- (SIMP_CONV (std_ss++WORD_BIT_EQ_ss) [] THENC tautLib.TAUT_CONV) “a && b && a = a && b”
<<HOL message: inventing new type variable names: 'a>>
> val it = |- (a && b && a = a && b) = T : thm
```

### Comments

This fragment is not included in `WORDS_ss`.

### See also

[`wordsLib.WORD_BIT_EQ_CONV`](#wordsLib.WORD_BIT_EQ_CONV),
[`fcpLib.FCP_ss`](#fcpLib.FCP_ss),
[`blastLib.BBLAST_CONV`](#blastLib.BBLAST_CONV),
[`wordsLib.BIT_ss`](#wordsLib.BIT_ss),
[`wordsLib.SIZES_ss`](#wordsLib.SIZES_ss),
[`wordsLib.WORD_ARITH_ss`](#wordsLib.WORD_ARITH_ss),
[`wordsLib.WORD_LOGIC_ss`](#wordsLib.WORD_LOGIC_ss),
[`wordsLib.WORD_SHIFT_ss`](#wordsLib.WORD_SHIFT_ss),
[`wordsLib.WORD_ARITH_EQ_ss`](#wordsLib.WORD_ARITH_EQ_ss),
[`wordsLib.WORD_EXTRACT_ss`](#wordsLib.WORD_EXTRACT_ss),
[`wordsLib.WORD_MUL_LSL_ss`](#wordsLib.WORD_MUL_LSL_ss),
[`wordsLib.WORD_ss`](#wordsLib.WORD_ss)
