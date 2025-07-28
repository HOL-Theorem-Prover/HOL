## `UNCURRY_EXISTS_CONV` {#PairRules.UNCURRY_EXISTS_CONV}


```
UNCURRY_EXISTS_CONV : conv
```



Uncurrys consecutive existential quantifications into
a paired existential quantification.

### Example

    
    - UNCURRY_EXISTS_CONV (Term `?x y. x + y = y + x`);
    > val it = |- (?x y. x + y = y + x) = ?(x,y). x + y = y + x : thm
    
    - UNCURRY_EXISTS_CONV (Term `?(w,x) (y,z). w+x+y+z = z+y+x+w`);
    > val it =
        |- (?(w,x) (y,z). w + x + y + z = z + y + x + w) =
           ?((w,x),y,z). w + x + y + z = z + y + x + w : thm
    



### Failure

`UNCURRY_EXISTS_CONV tm` fails if `tm` is not a
consecutive existential quantification.

### See also

[`PairRules.CURRY_CONV`](#PairRules.CURRY_CONV), [`PairRules.UNCURRY_CONV`](#PairRules.UNCURRY_CONV), [`PairRules.CURRY_EXISTS_CONV`](#PairRules.CURRY_EXISTS_CONV), [`PairRules.CURRY_FORALL_CONV`](#PairRules.CURRY_FORALL_CONV), [`PairRules.UNCURRY_FORALL_CONV`](#PairRules.UNCURRY_FORALL_CONV)

