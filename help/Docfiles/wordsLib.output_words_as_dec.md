## `output_words_as_dec`

``` hol4
wordsLib.output_words_as_dec : unit -> unit
```

------------------------------------------------------------------------

Makes word literals pretty-print as decimal.

A call to `output_words_as_dec` will make word literals output in
decimal format.

### Example

``` hol4
- “0x100000w”;
<<HOL message: inventing new type variable names: 'a>>
> val it = “0x100000w” : term
- wordsLib.output_words_as_dec();
- “0x100000w”;
<<HOL message: inventing new type variable names: 'a>>
> val it = “1048576w” : term
```

### See also

[`wordsLib.remove_word_printer`](#wordsLib.remove_word_printer),
[`wordsLib.output_words_as_hex`](#wordsLib.output_words_as_hex),
[`wordsLib.output_words_as_bin`](#wordsLib.output_words_as_bin),
[`wordsLib.output_words_as_oct`](#wordsLib.output_words_as_oct)
