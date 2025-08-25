## `notify_on_word_length_guess`

``` hol4
wordsLib.notify_on_word_length_guess : bool ref
```

------------------------------------------------------------------------

Controls notification of word length guesses.

When the reference `notify_on_word_length_guess` is true a HOL message
is printed (in interactive sessions) when the function
`inst_word_lengths` instantiates types in a term.

### Example

``` hol4
- load "wordsLib";
...
- wordsLib.notify_on_word_length_guess := false;
> val it = () : unit
- wordsLib.inst_word_lengths “(7 >< 5) a @@ (4 >< 0) a”;
<<HOL message: inventing new type variable names: 'a, 'b, 'c, 'd>>
> val it = “(7 >< 5) a @@ (4 >< 0) a” : term
- type_of it;
> val it = “:bool[8]” : hol_type
```

### Comments

By default `notify_on_word_length_guess` is true.

### See also

[`wordsLib.guess_lengths`](#wordsLib.guess_lengths),
[`wordsLib.inst_word_lengths`](#wordsLib.inst_word_lengths)
