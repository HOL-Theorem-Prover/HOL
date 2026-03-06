## `remove_word_printer`

``` hol4
wordsLib.remove_word_printer : unit -> unit
```

------------------------------------------------------------------------

Turns off custom pretty-printing for word literals.

The function `remove_word_printer` calls `Parse.remove_user_printer` to
remove pretty-printing for ground instances of "n2w n". This will
normally mean that words output in decimal format.

### Example

``` hol4
- load "wordsLib";
...
- “0x10000000w”;
<<HOL message: inventing new type variable names: 'a>>
> val it = “0x10000000w” : term
- wordsLib.remove_word_printer();
- “0x10000000w”;
<<HOL message: inventing new type variable names: 'a>>
> val it = “268435456w” : term
```

### See also

[`Parse.remove_user_printer`](#Parse.remove_user_printer),
[`wordsLib.output_words_as`](#wordsLib.output_words_as),
[`wordsLib.output_words_as_dec`](#wordsLib.output_words_as_dec),
[`wordsLib.output_words_as_bin`](#wordsLib.output_words_as_bin),
[`wordsLib.output_words_as_oct`](#wordsLib.output_words_as_oct),
[`wordsLib.output_words_as_hex`](#wordsLib.output_words_as_hex)
