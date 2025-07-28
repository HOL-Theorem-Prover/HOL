## `strcat` {#Lib.strcat}


```
strcat : string -> string -> string
```



Concatenates two ML strings.

### Failure

Never fails.

### Example

    
    - strcat "1" "";
    > val it = "1" : string
    
    - strcat "hello" "world";
    > val it = "helloworld" : string
    
    - strcat "hello" (strcat " " "world");
    > val it = "hello world" : string
    
