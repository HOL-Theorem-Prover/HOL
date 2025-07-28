## `IFC` {#Conv.IFC}


```
IFC : conv -> conv -> conv -> conv
```



Apply a conversion and branch to next conversion.


A call to `IFC c1 c2 c3 t` applies the conversion `c1` to `t`.
If this application succeeds (or raises `UNCHANGED`) then `c2` is applied next.
Otherwise, `c3` is applied to `t`.

### Failure

Fails when `c1` succeeds and `c2` fails, or when `c1` fails and `c3` fails.

### Example

    
       > IFC (RATOR_CONV BETA_CONV) BETA_CONV NO_CONV ``(\x y. x ==> y) T F``;
       val it = |- T ==> F : thm
    
The first `RATOR_CONV BETA_CONV` succeeds and chains successfully with the second `BETA_CONV`.

    
       > IFC ALL_CONV BETA_CONV (RATOR_CONV BETA_CONV) ``(\x y. x ==> y) T F``;
       Exception - BETA_CONV: not a beta redex
    
Although `ALL_CONV` succeeds, it does nothing, so `BETA_CONV` is not applicable.

    
       > IFC NO_CONV BETA_CONV (RATOR_CONV BETA_CONV) ``(\x y. x ==> y) T F``;
       val it = |- (\y. T ==> y) F : thm
    
The `NO_CONV` fails, so `RATOR_CONV BETA_CONV` applies.

### See also

[`Conv.ORELSEC`](#Conv.ORELSEC), [`Conv.REPEATC`](#Conv.REPEATC)

