## `WORD_DECIDE`

``` hol4
wordsLib.WORD_DECIDE : conv
```

------------------------------------------------------------------------

A decision procedure for words.

The conversion `WORD_DECIDE` is the same as
`WORD_DP WORD_CONV bossLib.DECIDE`.

### Example

``` hol4
- WORD_DECIDE “a && (b !! a) = a !! a && b”
<<HOL message: inventing new type variable names: 'a>>
> val it = |- a && (b !! a) = a !! a && b : thm

- WORD_DECIDE “a + 2w <+ 4w = a <+ 2w \/ 13w <+ a :word4”
> val it = |- a + 2w <+ 4w = a <+ 2w \/ 13w <+ a : thm

- WORD_DECIDE “a < 0w = 1w <+ a : word2”
> val it = |- a < 0w = 1w <+ a : thm

- WORD_DECIDE “(?w:word4. 14w <+ w) /\ ~(?w:word4. 15w <+ w)”
> val it = |- (?w. 14w <+ w) /\ ~ ?w. 15w <+ w : thm
```

### See also

[`wordsLib.WORD_DP`](#wordsLib.WORD_DP)
