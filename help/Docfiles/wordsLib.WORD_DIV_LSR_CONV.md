## `WORD_DIV_LSR_CONV`

``` hol4
wordsLib.WORD_DIV_LSR_CONV : conv
```

------------------------------------------------------------------------

The conversion `WORD_DIV_LSR_CONV` replaces instances of unsigned
division by a power of two with applications of logical right-shift.

### Example

``` hol4
> wordsLib.WORD_DIV_LSR_CONV “w // 8w : word8”;
val it = |- w // 8w = w >>> 3: thm
```

### Comments

This conversion requires the word length to be known.

### See also

[`wordsLib.WORD_MUL_LSL_CONV`](#wordsLib.WORD_MUL_LSL_CONV),
[`wordsLib.WORD_MOD_BITS_CONV`](#wordsLib.WORD_MOD_BITS_CONV)
