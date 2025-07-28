## `pbody` {#pairSyntax.pbody}


```
pbody : (term -> term)
```



Returns the body of a paired abstraction.


`pbody "\pair. t"` returns `"t"`.

### Failure

Fails unless the term is a paired abstraction.

### See also

[`Term.body`](#Term.body), [`pairSyntax.dest_pabs`](#pairSyntax.dest_pabs)

