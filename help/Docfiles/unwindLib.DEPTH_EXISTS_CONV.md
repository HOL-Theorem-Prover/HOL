## `DEPTH_EXISTS_CONV` {#unwindLib.DEPTH_EXISTS_CONV}


```
DEPTH_EXISTS_CONV : (conv -> conv)
```



Applies a conversion to the body of nested existential quantifications.


`DEPTH_EXISTS_CONV conv "?x1 ... xn. body"` applies `conv` to `"body"` and
returns a theorem of the form:
    
       |- (?x1 ... xn. body) = (?x1 ... xn. body')
    

### Failure

Fails if the application of `conv` fails.

### Example

    
    #DEPTH_EXISTS_CONV BETA_CONV "?x y z. (\w. x /\ y /\ z /\ w) T";;
    |- (?x y z. (\w. x /\ y /\ z /\ w)T) = (?x y z. x /\ y /\ z /\ T)
    

### See also

[`unwindLib.DEPTH_FORALL_CONV`](#unwindLib.DEPTH_FORALL_CONV)

