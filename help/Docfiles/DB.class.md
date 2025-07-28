## `class` {#DB.class}


```
datatype class
```



Datatype for classifying theory elements.


Many of the functions in the `DB` structure return answers that involve
the `class` type, which is declared as
    
       datatype class = Thm | Axm | Def
    
When occurring with `th`, an ML value of type `thm`,
`Axm` means that `th` has been asserted as an axiom; `Def` means that `th`
is a constant definition; and `Thm` means that `th` is a plain old theorem,
i.e,. not an axiom or a definition.

### See also

[`DB.data`](#DB.data)

