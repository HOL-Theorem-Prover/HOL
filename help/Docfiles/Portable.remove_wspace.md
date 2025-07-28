## `remove_wspace` {#Portable.remove_wspace}


```
remove_wspace : string -> string
```



Removes all whitespace characters from a string


A call to `remove_wspace s` returns a string identical to `s` except
that all of the characters for which `Char.isSpace` is true have been
removed. The implementation is 
    
       String.translate (fn c => if Char.isSpace c then "" else str c) s
    

### Failure

Never fails.

### See also

[`Portable.remove_external_wspace`](#Portable.remove_external_wspace)

