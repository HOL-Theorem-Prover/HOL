## `GSYM`

``` hol4
Conv.GSYM : thm -> thm
```

------------------------------------------------------------------------

Reverses the first equation(s) encountered in a top-down search.

The inference rule `GSYM` reverses the first equation(s) encountered in
a top-down search of the conclusion of the argument theorem. An equation
will be reversed iff it is not a proper subterm of another equation. If
a theorem contains no equations, it will be returned unchanged.

``` hol4
    A |- ..(s1 = s2)...(t1 = t2)..
   --------------------------------  GSYM
    A |- ..(s2 = s1)...(t2 = t1)..
```

### Failure

Never fails, and never loops infinitely.

### Example

``` hol4
- arithmeticTheory.ADD;
> val it = |- (!n. 0 + n = n) /\ (!m n. (SUC m) + n = SUC(m + n)) : thm

- GSYM arithmeticTheory.ADD;
> val it = |- (!n. n = 0 + n) /\ (!m n. SUC(m + n) = (SUC m) + n) : thm
```

### See also

[`Drule.NOT_EQ_SYM`](#Drule.NOT_EQ_SYM), [`Thm.REFL`](#Thm.REFL),
[`Thm.SYM`](#Thm.SYM)
