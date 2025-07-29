## `MP`

``` hol4
Thm.MP : thm -> thm -> thm
```

------------------------------------------------------------------------

Implements the Modus Ponens inference rule.

When applied to theorems `A1 |- t1 ==> t2` and `A2 |- t1`, the inference
rule `MP` returns the theorem `A1 u A2 |- t2`.

``` hol4
    A1 |- t1 ==> t2   A2 |- t1
   ----------------------------  MP
          A1 u A2 |- t2
```

In common with the underlying `dest_imp` syntax function, `MP` treats
theorems with conclusions of the form `~p` as implications `p ==> F`.
This means that `MP` also has the following behaviour:

``` hol4
    A1 |- ~t1     A2 |- t1
   ------------------------  MP
         A1 u A2 |- F
```

### Failure

Fails unless the first theorem is an implication (in the sense of
`dest_imp`) whose antecedent is the same as the conclusion of the second
theorem (up to alpha-conversion)

### See also

[`boolSyntax.dest_imp`](#boolSyntax.dest_imp),
[`Thm.EQ_MP`](#Thm.EQ_MP), [`Drule.LIST_MP`](#Drule.LIST_MP),
[`Drule.MATCH_MP`](#Drule.MATCH_MP),
[`Tactic.MATCH_MP_TAC`](#Tactic.MATCH_MP_TAC),
[`Tactic.MP_TAC`](#Tactic.MP_TAC)
