## `bool_EQ_CONV` {#Conv.bool_EQ_CONV}


```
bool_EQ_CONV : conv
```



Simplifies expressions involving boolean equality.


The conversion `bool_EQ_CONV` simplifies equations of the form `t1 = t2`,
where `t1` and `t2` are of type `bool`.  When applied to a term of the form
`t = t`, the conversion `bool_EQ_CONV` returns the theorem
    
       |- (t = t) = T
    
When applied to a term of the form `t = T`, the conversion returns
    
       |- (t = T) = t
    
And when applied to a term of the form `T = t`, it returns
    
       |- (T = t) = t
    



### Failure

Fails unless applied to a term of the form `t1 = t2`, where `t1` and `t2` are
boolean, and either `t1` and `t2` are syntactically identical terms or one of
`t1` and `t2` is the constant `T`.

### Example

    
    - bool_EQ_CONV (Parse.Term `T = F`);
    val it = |- (T = F) = F : thm
    
    - bool_EQ_CONV (Parse.Term `(0 < n) = T`);
    val it = |- (0 < n = T) = 0 < n : thm
    


