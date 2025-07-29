## `Abbr`

``` hol4
BasicProvers.Abbr : term quotation -> thm
```

------------------------------------------------------------------------

Signals to simplification tactics that an abbreviation should be used.

The `Abbr` function is used to signal to various simplification tactics
that an abbreviation in the current goal should be eliminated before
simplification proceeds. Each theorem created by `Abbr` is removed from
the tactic's theorem-list argument, and causes a call to
`Q.UNABBREV_TAC` with that `Abbr` theorem's argument. Finally, the
simplification tactic continues, with the rest of the theorem-list as
its argument. Thus,

``` hol4
   tac [..., Abbr`v`, ..., Abbr`u`, ...]
```

has the same effect as

``` hol4
   Q.UNABBREV_TAC `v` THEN Q.UNABBREV_TAC `u` THEN
   tac [..., ..., ...]
```

Every theorem created by `Abbr` in the argument list is treated in this
way. The tactics that understand `Abbr` arguments are `SIMP_TAC`,
`ASM_SIMP_TAC`, `FULL_SIMP_TAC`, `RW_TAC` and `SRW_TAC`.

### Failure

`Abbr` itself never fails, but the tactic it is used in may do,
particularly if the induced calls to `UNABBREV_TAC` fail.

### Comments

This function is a notational convenience that allows the effect of
multiple tactics to be packaged into just one.

### See also

[`Q.ABBREV_TAC`](#Q.ABBREV_TAC),
[`simpLib.SIMP_TAC`](#simpLib.SIMP_TAC),
[`Q.UNABBREV_TAC`](#Q.UNABBREV_TAC)
