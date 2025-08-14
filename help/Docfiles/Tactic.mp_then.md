## `mp_then`

``` hol4
Tactic.mp_then : match_position -> thm_tactic -> thm -> thm -> tactic
```

------------------------------------------------------------------------

Matches two theorems against each other and then continues

The `mp_then` tactic combines two theorems (one or both of which will
typically come from the current goal's assumptions) using modus ponens
in a controlled way, and then passes the result of this to a
continuation theorem-tactic.

Thus `mp_then ttac pos ith th` is a tactic in the usual "`_then`"
fashion which produces a theorem and then applies the `ttac`
continuation to that result. The theorems `ith` and `th` are the two
theorems: `ith` contains the implication, and the other has a conclusion
matching one of the antecedents of the implication.

An implication's antecedents are calculated by first normalising the
implication so that it is of the form

``` hol4
  !v1 .. vn. ant1 /\ ant2 .. /\ antn ==> concl
```

The `pos` parameter indicates how to find the antecedent. There are four
possible forms for `pos` (constructors for the `match_position` type).
It can be `Any`, which tells `mp_then` to search for anything that
works. It can be `Pat q`, with `q` a quotation, which means to find
anything matching `q` that works. It can be `Pos f`, where `f` is a
function of type `term list -> term`, and is typically a value such as
`hd`, `el n` for some number `n` or `last`. This function is passed the
list of all `ith`'s antecedents to pick the right one. Finally, the
`pos` parameter might be `Concl`, meaning that the conclusion of `ith`
is treated as a negated assumption. This allows implications to be used
in a contrapositive way.

In practice, there are some common patterns for obtaining `ith` and
`th`. Apart from the fully applied version above, you might also see:

``` hol4
   <sel>_assum (mp_then pos ttac ith)

   <sel>_assum (<sel>_assum o mp_then pos ttac)

   disch_then(<sel>_assum o mp_then pos ttac)
```

where `<sel>` is one of `first`, `last`, `qpat` and `goal`, possibly
with an appended `_x`; the usual ways of obtaining theorems from the
current goal. Where there are two selectors used, the outermost is used
for the selection of the implicational theorem and the innermost selects
`th`. In the first example, the `ith` value is provided in the call, and
is presumably an existing theorem rather than an assumption from the
goal.

The `goal_assum` selector is worth special mention since it's especially
useful with `mp_then`: it turns an existentially quantified goal
`?x. P x` into the assumption `!x. P x ==> F` thereby providing a
theorem with antecedents to match on. In conjunction with `mp_tac`
(which will put the revised implication back into the goal as an
existential once more) it has the effect of instantiating the
existential quantifier in order to match a provided subterm (similar to
`part_match_exists_tac` or `asm_exists_tac`).

Finally, note that the `Pat` and `Any` position selectors will backtrack
across the set of theorem antecedents to find a match that makes the
whole application succeed.

### Failure

If the provided implicational theorem doesn't have a match at a
compatible position for the second provided theorem, or if no such match
then allows the continuation `ttac` to succeed.

### See also

[`Tactical.goal_assum`](#Tactical.goal_assum),
[`Tactic.resolve_then`](#Tactic.resolve_then)
