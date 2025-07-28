## `SIZES_CONV` {#wordsLib.SIZES_CONV}


```
SIZES_CONV : conv
```



Evaluates `dimindex`, `dimword` and `INT_MIN`.

### Example

    
    - SIZES_CONV “dimword(:32)”
    > val it = |- dimword (:32) = 4294967296 : thm
    

### Comments

Evaluations are stored and so will be slightly faster when repeated.

### See also

[`wordsLib.SIZES_ss`](#wordsLib.SIZES_ss)

