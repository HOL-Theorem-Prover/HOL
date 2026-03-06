## `THEN_TCL`

``` hol4
Thm_cont.THEN_TCL : (thm_tactical * thm_tactical -> thm_tactical)
```

------------------------------------------------------------------------

Composes two theorem-tacticals.

If `ttl1` and `ttl2` are two theorem-tacticals, `ttl1 THEN_TCL ttl2` is
a theorem-tactical which composes their effect; that is, if:

``` hol4
   ttl1 ttac th1 = ttac th2
```

and

``` hol4
   ttl2 ttac th2 = ttac th3
```

then

``` hol4
   (ttl1 THEN_TCL ttl2) ttac th1 = ttac th3
```

### Failure

The application of `THEN_TCL` to a pair of theorem-tacticals never
fails.

### See also

[`Thm_cont.EVERY_TCL`](#Thm_cont.EVERY_TCL),
[`Thm_cont.FIRST_TCL`](#Thm_cont.FIRST_TCL),
[`Thm_cont.ORELSE_TCL`](#Thm_cont.ORELSE_TCL)
