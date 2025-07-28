## `Induct_word` {#wordsLib.Induct_word}


```
Induct_word : tactic
```



Initiate an induction on the value of a word.


The tactic `Induct_word` makes use of the tactic
`bossLib.recInduct wordsTheory.WORD_INDUCT`.

### Example

Given the goal
    
    ?- !w:word8. P w
    
one can apply `Induct_word` to begin a proof by induction.
    
    - e Induct_word
    
This results in the base and step cases of the induction as new goals.
    
    ?- P 0w
    
    [SUC n < 256, P (n2w n)] ?- P (n2w (SUC n))
    

### See also

[`bossLib.recInduct`](#bossLib.recInduct)

