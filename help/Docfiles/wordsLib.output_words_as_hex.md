## `output_words_as_hex`

``` hol4
wordsLib.output_words_as_hex : unit -> unit
```

------------------------------------------------------------------------

Makes word literals pretty-print as hexadecimal.

A call to `output_words_as_hex` will make word literals output in
hexadecimal format.

### Example

``` hol4
- wordsLib.output_words_as_hex();
- EVAL “44w : word32 << 3”
> val it = |- 0x2Cw << 3 = 0x160w : thm
```

### See also

[`wordsLib.remove_word_printer`](#wordsLib.remove_word_printer),
[`wordsLib.output_words_as_dec`](#wordsLib.output_words_as_dec),
[`wordsLib.output_words_as_bin`](#wordsLib.output_words_as_bin),
[`wordsLib.output_words_as_oct`](#wordsLib.output_words_as_oct)
