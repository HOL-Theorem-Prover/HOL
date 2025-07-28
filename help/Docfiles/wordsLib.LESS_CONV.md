## `LESS_CONV` {#wordsLib.LESS_CONV}


```
LESS_CONV : conv
```



Converts terms of the form `n < m` into
`(n = m - 1) \/ ... \/ (n = 1) \/ (n = 0)`, provided that `m` is a natural
number literal.

### Example

    
    > wordsLib.LESS_CONV “n < 4n”;
    val it =
       |- n < 4 <=> (n = 3) \/ (n = 2) \/ (n = 1) \/ (n = 0):
       thm
    
