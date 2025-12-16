## `WORD_DP`

``` hol4
wordsLib.WORD_DP : conv -> conv -> conv
```

------------------------------------------------------------------------

Constructs a decision procedure for words.

The conversion `WORD_DP conv dp` is a decision procedure for words that
makes use of the supplied conversion `conv` and decision procedure `dp`.
Suitable decision procedures include `tautLib.TAUT_PROVE`,
`bossLib.DECIDE`, `intLib.ARITH_PROVE` and `intLib.COOPER_PROVE`. The
procedure will first apply `conv` and then `WORD_BIT_EQ_CONV`. If this
is not sufficient then an attempt is made to solve the problem by
applying an arithmetic decision procedure `dp`,
e.g. `“(a = 0w) \/ (a = 1w :1 word)”` is mapped to the goal
`“w2n a < 2 ==> (w2n a = 0) \/ (w2n a = 1)”`.

### Failure

The invocation will fail when the decision procedure `dp` fails.

### Example

``` hol4
- wordsLib.WORD_DP ALL_CONV tautLib.TAUT_PROVE “a && b && a = a && b”
<<HOL message: inventing new type variable names: 'a>>
> val it = |- a && b && a = a && b : thm

- wordsLib.WORD_DP ALL_CONV DECIDE “a < b /\ b < c ==> a < c : 'a word”
> val it = |- a < b /\ b < c ==> a < c : thm

- wordsLib.WORD_DP ALL_CONV intLib.ARITH_PROVE “a <+ 3w:word16 ==> (a = 0w) \/ (a = 1w) \/ (a = 2w)”
> val it = |- a <+ 3w ==> (a = 0w) \/ (a = 1w) \/ (a = 2w) : thm
```

### Comments

On large problems `intLib.ARITH_PROVE` will perform much better than
`bossLib.DECIDE`.

### See also

[`wordsLib.WORD_BIT_EQ_CONV`](#wordsLib.WORD_BIT_EQ_CONV),
[`wordsLib.WORD_DECIDE`](#wordsLib.WORD_DECIDE)
