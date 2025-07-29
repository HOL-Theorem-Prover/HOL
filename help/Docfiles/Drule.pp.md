## `pp`

``` hol4
Drule.pp : thmpos_dtype.match_position -> thm -> thm
```

------------------------------------------------------------------------

Promotes the designated premise to the "top" of an implicational
theorem.

A call to `pp pos th` finds the premise denoted by `pos` in `th` and
promotes it so that it occurs as the outermost antecedent of the
theorem. The theorem argument `th` is first normalised by a call to
`MP_CANON`.

Any theorem whose top level operator (after universal quantifiers are
stripped away) is an implication can be viewed as being of the form

``` hol4
   ∀v1 .. vn. p1 /\ p2 /\ .. pn ==> c
```

where the variables `v1` to `vn` may be free in some of the antecedents
and/or conclusion `c`. To promote a premise `pi` transforms the above
into

``` hol4
   ∀va .. vk. pi ==> ∀vx .. vz. pa /\ pb ... /\ pj ==> c
```

The four constructors of the `match_position` type can be used to
designate different premises. The `Pos f` form applies the function `f`
to the list of premises, and is expected to return a member of the given
list. The `Pat q` form finds the first premise that matches the given
quotation pattern. In this context, `Any` is viewed as a synonym for
`Pos hd`. Finally, the `Concl` form selects the conclusion of the
theorem, and "promotes" it by taking the contrapositive of the theorem.

After promotion some cleanup is performed. If a contrapositive was
taken, double negations in the promoted premise are removed, and in all
cases, universal quantifiers of variables not present in the promoted
premise are pushed down to govern other premises.

### Failure

Fails if the provided match position does not denote a premise present
in the given theorem.

### Example

``` hol4
> sortingTheory.ALL_DISTINCT_PERM;
val it = ⊢ ∀l1 l2. PERM l1 l2 ⇒ (ALL_DISTINCT l1 ⇔ ALL_DISTINCT l2)

> it |> iffLR |> pp (Pos last);
val it = ⊢ ∀l1. ALL_DISTINCT l1 ⇒ ∀l2. PERM l1 l2 ⇒ ALL_DISTINCT l2: thm
```

### See also

[`Drule.MP_CANON`](#Drule.MP_CANON), [`Tactic.mp_then`](#Tactic.mp_then)
