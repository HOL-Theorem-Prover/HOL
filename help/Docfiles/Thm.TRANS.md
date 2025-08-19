## `TRANS`

``` hol4
Thm.TRANS : (thm -> thm -> thm)
```

------------------------------------------------------------------------

Uses transitivity of equality on two equational theorems.

When applied to a theorem `A1 |- t1 = t2` and a theorem `A2 |- t2 = t3`,
the inference rule `TRANS` returns the theorem `A1 u A2 |- t1 = t3`.

``` hol4
    A1 |- t1 = t2   A2 |- t2 = t3
   -------------------------------  TRANS
         A1 u A2 |- t1 = t3
```

### Failure

Fails unless the theorems are equational, with the right side of the
first being the same as the left side of the second.

### Example

``` hol4
   - val t1 = ASSUME ``a:bool = b`` and t2 = ASSUME ``b:bool = c``;
   val t1 = [.] |- a = b : thm
   val t2 = [.] |- b = c : thm

   - TRANS t1 t2;
   val it = [..] |- a = c : thm
```

### See also

[`Thm.EQ_MP`](#Thm.EQ_MP), [`Drule.IMP_TRANS`](#Drule.IMP_TRANS),
[`Thm.REFL`](#Thm.REFL), [`Thm.SYM`](#Thm.SYM)
