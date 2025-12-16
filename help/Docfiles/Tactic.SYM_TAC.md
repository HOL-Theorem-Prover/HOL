## `SYM_TAC`

``` hol4
Tactic.SYM_TAC : tactic
```

------------------------------------------------------------------------

Flips an equality at the top-level of a goal

An application of `SYM_TAC` behaves as follows:

``` hol4
     G  ?-   x = y
   =================   SYM_TAC
     G  ?-   y = x
```

### Failure

Fails if the goal is not an equality.

### Comments

Also available as the alias `sym_tac`.

### See also

[`Tactic.REFL_TAC`](#Tactic.REFL_TAC), [`Thm.SYM`](#Thm.SYM)
