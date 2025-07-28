## `EXISTS_AND_REORDER_CONV` {#Conv.EXISTS_AND_REORDER_CONV}


```
EXISTS_AND_REORDER_CONV : conv
```



Moves an existential quantification inwards through a conjunction,
sorting the body.


When applied to a term of the form `?x. c1 /\ c2 /\ .. /\ cn`, where
`x` is not free in at least one of the conjuncts `ci`, then
`EXISTS_AND_REORDER_CONV` returns a theorem of the form
    
       |- (?x. ...) = (ci /\ cj /\ ck /\ ...) /\ (?x. cm /\ cn /\ cp /\ ...)
    
where the conjuncts `ci`, `cj` and `ck` do not have the bound variable
`x` free, and where the conjuncts `cm`, `cn` and `cp` do.

### Failure

`EXISTS_AND_REORDER_CONV` fails if it is applied to a term that is not
an existential.  It raises `UNCHANGED` if the existential’s body is
not a conjunction, or if the body does not have any conjuncts where
the bound variable does not occur, or if none of the body’s conjuncts
have free occurrences of the bound variable.

### Comments

The conjuncts in the resulting term are kept in the same relative
order as in the input term, but will all be right-associated in the
two groups (because they are re-assembled with `list_mk_conj`),
possibly destroying structure that existed in the original.

### See also

[`Conv.EXISTS_AND_CONV`](#Conv.EXISTS_AND_CONV)

