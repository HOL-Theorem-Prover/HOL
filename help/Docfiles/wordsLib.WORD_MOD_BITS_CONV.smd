## `WORD_MOD_BITS_CONV`

``` hol4
wordsLib.WORD_MOD_BITS_CONV : conv
```

------------------------------------------------------------------------

The conversion `WORD_MOD_BITS_CONV` replaces instances of `word_mod` by
a power of two with applications of `word_bits`.

### Example

``` hol4
> wordsLib.WORD_MOD_BITS_CONV “word_mod w 8w : word16”;
val it = |- word_mod w 8w = (2 -- 0) w: thm

wordsLib.WORD_MOD_BITS_CONV “word_mod w 1w : word16”;
val it = |- word_mod w 1w = 0w: thm
```

### Comments

This conversion requires the word length to be known.

### See also

[`wordsLib.WORD_DIV_LSR_CONV`](#wordsLib.WORD_DIV_LSR_CONV),
[`wordsLib.BITS_INTRO_CONV`](#wordsLib.BITS_INTRO_CONV)
