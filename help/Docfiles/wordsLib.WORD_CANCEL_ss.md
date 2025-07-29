## `WORD_CANCEL_ss`

``` hol4
wordsLib.WORD_CANCEL_ss : ssfrag
```

------------------------------------------------------------------------

Simplification fragment for words.

The fragment `WORD_CANCEL_ss` helps simplify linear equations over
bit-vectors. This fragment is designed to work in concert with
`wordsLib.WORD_ARITH_ss`. The procedure will endeavour to ensure that
all coefficients appear in positive form. Furthermore, the leftmost
coefficient will be highest on the left-hand side of equations.

### Example

``` hol4
> SIMP_CONV (pure_ss++wordsLib.WORD_ARITH_ss++wordsLib.WORD_CANCEL_ss) []
   “-3w * b + a = -2w * a + b: word32”;
val it =
   |- (-3w * b + a = -2w * a + b) <=> (4w * b = 3w * a):
   thm
```

### Comments

This fragment can be viewed as a superior version of
`wordsLib.WORD_ARITH_EQ_ss`.

### See also

[`wordsLib.WORD_ARITH_ss`](#wordsLib.WORD_ARITH_ss),
[`wordsLib.WORD_ARITH_EQ_ss`](#wordsLib.WORD_ARITH_EQ_ss)
