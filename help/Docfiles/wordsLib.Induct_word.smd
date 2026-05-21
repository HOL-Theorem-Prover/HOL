## `Induct_word`

``` hol4
wordsLib.Induct_word : tactic
```

------------------------------------------------------------------------

Initiate an induction on the value of a word.

The tactic `Induct_word` makes use of the tactic
`bossLib.recInduct wordsTheory.WORD_INDUCT`.

### Example

Given the goal

``` hol4
?- !w:word8. P w
```

one can apply `Induct_word` to begin a proof by induction.

``` hol4
- e Induct_word
```

This results in the base and step cases of the induction as new goals.

``` hol4
?- P 0w

[SUC n < 256, P (n2w n)] ?- P (n2w (SUC n))
```

### See also

[`bossLib.recInduct`](#bossLib.recInduct)
