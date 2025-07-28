## `type_of` {#Term.type_of}


```
type_of : term -> hol_type
```



Returns the type of a term.

### Failure

Never fails.

### Example

    
    - type_of boolSyntax.universal;
    > val it = `:('a -> bool) -> bool` : hol_type
    


