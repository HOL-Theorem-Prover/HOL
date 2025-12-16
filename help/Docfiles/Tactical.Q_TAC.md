## `Q_TAC`

``` hol4
Tactical.Q_TAC : (term -> tactic) -> term quotation -> tactic
```

------------------------------------------------------------------------

A tactical that parses in the context of a goal, a la the Q library.

When applied to a term tactic `T` and a quotation `q`, the tactic
`Q_TAC T q` first parses the quotation `q` in the context of the goal to
yield the term `tm`, and then applies the tactic `T tm` to the goal.

### Failure

The application of `Q_TAC` to a term tactic `T` and a quotation `q`
never fails. The resulting composite tactic `Q_TAC T q` fails when
applied to a goal if either `q` cannot be parsed, or `T tm` fails when
applied to the goal.

### Comments

Useful for avoiding decorating terms with type abbreviations.

### See also

[`Tactical.EVERY`](#Tactical.EVERY),
[`Tactical.FIRST`](#Tactical.FIRST),
[`Tactical.ORELSE`](#Tactical.ORELSE),
[`Tactical.THEN`](#Tactical.THEN), [`Tactical.THEN1`](#Tactical.THEN1),
[`Tactical.THENL`](#Tactical.THENL)
