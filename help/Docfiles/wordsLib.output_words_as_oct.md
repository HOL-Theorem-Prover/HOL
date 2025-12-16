## `output_words_as_oct`

``` hol4
wordsLib.output_words_as_oct : unit -> unit
```

------------------------------------------------------------------------

Makes word literals pretty-print as octal.

A call to `output_words_as_oct` will make word literals output in octal
format.

### Example

``` hol4
- “032w:word5”;
> val it = “32w” : term
- wordsLib.output_words_as_oct();
- “032w:word5”;
> val it = “032w” : term
- wordsLib.output_words_as_dec();
- “032w:word5”;
> val it = “26w” : term
```

### Comments

Printing and parsing in octal is controlled by the reference
`base_tokens.allow_octal_input`. A call to `output_words_as_oct` sets
this value to true.

### See also

[`wordsLib.remove_word_printer`](#wordsLib.remove_word_printer),
[`wordsLib.output_words_as_dec`](#wordsLib.output_words_as_dec),
[`wordsLib.output_words_as_bin`](#wordsLib.output_words_as_bin),
[`wordsLib.output_words_as_hex`](#wordsLib.output_words_as_hex)
