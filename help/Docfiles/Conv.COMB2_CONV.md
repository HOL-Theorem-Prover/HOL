## `COMB2_CONV` {#Conv.COMB2_CONV}


```
COMB2_CONV : conv * conv -> conv
```



Applies two conversions to an application’s subterms.


A call to `COMB2_CONV(c1,c2) t`, when `t` is an application term of
the form `f x`, causes conversion `c1` to be applied to term `f`, and
conversion `c2` to be applied to term `x`. If the results of these
calls are theorems of the form `|- f = f’` and `|- x = x’`, then the
result of the call to `COMB2_CONV` is the theorem `|- f x = f’ x’`.

If one of the two sub-calls raises the `UNCHANGED` exception, then the
result of that call is taken to be the reflexive theorem (`|- x = x`
if `c2` raises the exception, for example). If both conversions raise
the `UNCHANGED` exception, then so too does `COMB2_CONV(c1,c2) t`.

### Failure

Fails if the term is not a combination term, or if either conversion fails when applied to the respective sub-terms.

### Example

    
    > COMB2_CONV (ALL_CONV, numLib.REDUCE_CONV) ``f (10 * 3)``;
    <<HOL message: inventing new type variable names: 'a>>
    val it = |- f (10 * 3) = f 30 : thm
    

### See also

[`Conv.ABS_CONV`](#Conv.ABS_CONV), [`Conv.COMB_CONV`](#Conv.COMB_CONV), [`Conv.FORK_CONV`](#Conv.FORK_CONV), [`Conv.RAND_CONV`](#Conv.RAND_CONV), [`Conv.RATOR_CONV`](#Conv.RATOR_CONV)

