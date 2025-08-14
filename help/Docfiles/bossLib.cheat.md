## `cheat`

``` hol4
bossLib.cheat : tactic
```

------------------------------------------------------------------------

Discharge a goal without proving it.

The `cheat` tactic solves the current goal immediately without proving
it, using `mk_oracle_thm` and adding the `"cheat"` tag to any theorem
thereby obtained.

### Failure

Never fails.

### Comments

The intended use of `cheat` is to temporarily plug gaps in large theory
developments in order to sketch the bigger picture before filling in the
details. It can be useful as a kind of high-level `SUFF_TAC`: cheat on a
difficult lemma, see whether it works as intended for the main theorem,
then go back and prove the lemma properly.

The usual caveats associated with `mk_oracle_thm` apply: cheating
exposes you to the possibility of false theorems and contradictions. To
be sure a theorem was proved without cheating, check its tags.

### See also

[`Thm.mk_oracle_thm`](#Thm.mk_oracle_thm), [`Thm.tag`](#Thm.tag),
[`Globals.show_tags`](#Globals.show_tags),
[`Tactic.SUFF_TAC`](#Tactic.SUFF_TAC)
