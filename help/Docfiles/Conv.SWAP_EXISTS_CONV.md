## `SWAP_EXISTS_CONV` {#Conv.SWAP_EXISTS_CONV}


```
SWAP_EXISTS_CONV : conv
```



Interchanges the order of two existentially quantified variables.


When applied to a term argument of the form `?x y. P`, the conversion
`SWAP_EXISTS_CONV` returns the theorem:
    
       |- (?x y. P) = (?y x. P)
    



### Failure

`SWAP_EXISTS_CONV` fails if applied to a term that is not of the form
`?x y. P`.
