## `output_words_as_bin`

``` hol4
wordsLib.output_words_as_bin : unit -> unit
```

------------------------------------------------------------------------

Makes word literals pretty-print as binary.

A call to `output_words_as_bin` will make word literals output in binary
format.

### Example

``` hol4
- wordsLib.output_words_as_bin();
- EVAL “$FCP ODD : word8”;
> val it = |- $FCP ODD = 0b10101010w : thm
```

### See also

[`wordsLib.remove_word_printer`](#wordsLib.remove_word_printer),
[`wordsLib.output_words_as_dec`](#wordsLib.output_words_as_dec),
[`wordsLib.output_words_as_oct`](#wordsLib.output_words_as_oct),
[`wordsLib.output_words_as_hex`](#wordsLib.output_words_as_hex)
