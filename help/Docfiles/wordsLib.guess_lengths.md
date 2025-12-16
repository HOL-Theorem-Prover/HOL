## `guess_lengths`

``` hol4
wordsLib.guess_lengths : unit -> unit
```

------------------------------------------------------------------------

Turns on word length guessing.

A call to `guess_lengths` adds a post-prcessing stage to the term
parser: the function `inst_word_lengths` is used to instantiate type
variables that are the return type of `word_concat` and `word_extract`.

### Example

``` hol4
- load "wordsLib";
...
- show_types := true;
> val it = () : unit
- “(7 >< 5) a @@ (4 >< 0) a”;
<<HOL message: inventing new type variable names: 'a, 'b, 'c, 'd>>
> val it =
    “(((7 :num) >< (5 :num)) (a :bool['d]) :bool['a]) @@
      (((4 :num) >< (0 :num)) a :bool['b])” : term
- wordsLib.guess_lengths();
> val it = () : unit
- “(7 >< 5) a @@ (4 >< 0) a”;
<<HOL message: inventing new type variable names: 'a, 'b, 'c, 'd>>
<<HOL message: assigning word length(s): 'a <- 3, 'b <- 5 and 'c <- 8>>
> val it =
    “(((7 :num) >< (5 :num)) (a :bool['d]) :bool[3]) @@
      (((4 :num) >< (0 :num)) a :bool[5])” : term
- type_of it;
> val it = “:bool[8]” : hol_type
```

### See also

[`wordsLib.inst_word_lengths`](#wordsLib.inst_word_lengths),
[`wordsLib.notify_on_word_length_guess`](#wordsLib.notify_on_word_length_guess)
