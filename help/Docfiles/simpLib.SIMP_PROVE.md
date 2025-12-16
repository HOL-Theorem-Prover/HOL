## `SIMP_PROVE`

``` hol4
simpLib.SIMP_PROVE : simpset -> thm list -> term -> thm
```

------------------------------------------------------------------------

Like `SIMP_CONV`, but converts boolean terms to theorem with same
conclusion.

`SIMP_PROVE ss thml` is equivalent to `EQT_ELIM o SIMP_CONV ss thml`.

### Failure

Fails if the term can not be shown to be equivalent to true. May
diverge.

### Example

Applying the tactic

``` hol4
   ASSUME_TAC (SIMP_PROVE arith_ss [] ``x < y ==> x < y + 6``)
```

to the goal `?- x + y = 10` yields the new goal

``` hol4
   x < y ==> x < y + 6 ?- x + y = 10
```

Using `SIMP_PROVE` here allows `ASSUME_TAC` to add a new fact, where the
equality with truth that `SIMP_CONV` would produce would be less useful.

`SIMP_PROVE` is useful when constructing theorems to be passed to other
tools, where those other tools would prefer not to have theorems of the
form `|- P = T`.

### See also

[`simpLib.SIMP_CONV`](#simpLib.SIMP_CONV),
[`simpLib.SIMP_RULE`](#simpLib.SIMP_RULE),
[`simpLib.SIMP_TAC`](#simpLib.SIMP_TAC)
