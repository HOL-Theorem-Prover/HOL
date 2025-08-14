## `EVERY_TCL`

``` hol4
Thm_cont.EVERY_TCL : (thm_tactical list -> thm_tactical)
```

------------------------------------------------------------------------

Composes a list of theorem-tacticals.

When given a list of theorem-tacticals and a theorem, `EVERY_TCL` simply
composes their effects on the theorem. The effect is:

``` hol4
   EVERY_TCL [ttl1;...;ttln] = ttl1 THEN_TCL ... THEN_TCL ttln
```

In other words, if:

``` hol4
   ttl1 ttac th1 = ttac th2  ...  ttln ttac thn = ttac thn'
```

then:

``` hol4
   EVERY_TCL [ttl1;...;ttln] ttac th1 = ttac thn'
```

If the theorem-tactical list is empty, the resulting theorem-tactical
behaves in the same way as `ALL_THEN`, the identity theorem-tactical.

### Failure

The application to a list of theorem-tacticals never fails.

### See also

[`Thm_cont.FIRST_TCL`](#Thm_cont.FIRST_TCL),
[`Thm_cont.ORELSE_TCL`](#Thm_cont.ORELSE_TCL),
[`Thm_cont.REPEAT_TCL`](#Thm_cont.REPEAT_TCL),
[`Thm_cont.THEN_TCL`](#Thm_cont.THEN_TCL)
