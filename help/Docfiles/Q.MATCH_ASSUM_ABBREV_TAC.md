## `MATCH_ASSUM_ABBREV_TAC` {#Q.MATCH_ASSUM_ABBREV_TAC}


```
Q.MATCH_ASSUM_ABBREV_TAC : term quotation -> tactic
```



Introduces abbreviations by matching a pattern against an assumption.


When applied to the goal `(asl, w)`, the tactic `Q.MATCH_ASSUM_ABBREV_TAC q`
parses the quotation `q` in the context of the goal, producing a term to use as
a pattern. The tactic then attempts a (first order) match of the pattern
against each term in `asl`, stopping on the first matching assumption `a`.
Variables that occur in both the pattern and the goal are treated as “local
constants”, and will not acquire instantiations.

For each variable `v` in the pattern that has not been treated as a local
constant, there will be an instantiation term `t`, such that the substitution
`pattern[v1 |-> t1, v2 |-> t2, ...]` produces `a`. The effect of the tactic is
to then perform abbreviations in the goal, replacing each `t` with the
corresponding `v`, and adding assumptions of the form `Abbrev(v = t)` to the
goal.

### Failure

`MATCH_ABBREV_TAC` fails if the pattern provided does not match any assumption,
or if variables from the goal are used in the pattern in ways that make the
pattern fail to type-check.

### Comments

This tactic improves on the following tedious workflow:
`Q.PAT_ASSUM pat MP_TAC`, `` Q.MATCH_ABBREV_TAC `pat ==> X` ``, `` Q.UNABBREV_TAC `X` ``,
`STRIP_TAC`.

### See also

[`Q.MATCH_ABBREV_TAC`](#Q.MATCH_ABBREV_TAC), [`Q.MATCH_ASSUM_RENAME_TAC`](#Q.MATCH_ASSUM_RENAME_TAC)

