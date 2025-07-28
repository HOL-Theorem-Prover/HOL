## `quote` {#Lib.quote}


```
quote : string -> string
```



Put quotation marks around a string.


An application `quote s` is equal to `"\"" ^ s ^ "\""`. This is often
useful when printing messages.

### Failure

Never fails

### Example

    
    - print "foo\n";
    foo
    > val it = () : unit
    
    - print (quote "foo" ^ "\n");
    "foo"
    > val it = () : unit
    



### See also

[`Lib.mlquote`](#Lib.mlquote)

