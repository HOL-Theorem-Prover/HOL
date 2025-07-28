## `LEFT_OR_EXISTS_CONV` {#Conv.LEFT_OR_EXISTS_CONV}


```
LEFT_OR_EXISTS_CONV : conv
```



Moves an existential quantification of the left disjunct outwards through a
disjunction.


When applied to a term of the form `(?x.P) \/ Q`, the conversion
`LEFT_OR_EXISTS_CONV` returns the theorem:
    
       |- (?x.P) \/ Q = (?x'. P[x'/x] \/ Q)
    
where `x'` is a primed variant of `x` that does not appear free in
the input term.

### Failure

Fails if applied to a term not of the form `(?x.P) \/ Q`.

### See also

[`Conv.EXISTS_OR_CONV`](#Conv.EXISTS_OR_CONV), [`Conv.OR_EXISTS_CONV`](#Conv.OR_EXISTS_CONV), [`Conv.RIGHT_OR_EXISTS_CONV`](#Conv.RIGHT_OR_EXISTS_CONV)

