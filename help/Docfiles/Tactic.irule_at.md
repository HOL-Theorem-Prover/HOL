## `irule_at`

``` hol4
Tactic.irule_at : match_position -> thm -> tactic
```

------------------------------------------------------------------------

Applies an implicational theorem backwards in a particular position in
the goal

A call to `irule_at pos th`, with `th` an "implicational" theorem of
general form `∀xs... P ⇒ Q`, will attempt to find an instance of term
`Q` at position `pos` within the current goal, and replace it with an
appropriately instantiated version of `P`. (It is possible for `P` to be
empty, in which case the term is effectively replaced by truth.) The
possible positions encoded by `pos` are all "positive", meaning that
this process is sound (it may nonetheless turn a provable goal into an
unprovable one).

The possible positions encoded by parameter `pos` view the goal as if it
is of form `?ys. c1 ∧ ... ∧ cn`, where the existential prefix `ys` may
be empty, and where there may only be one conjunct. If `pos` encodes the
choice of conjunct `cj`, then `irule_at pos` will instantiate type
variables and term variables from `xs` in `th`, and variables from `ys`
in the goal so as to make `cj` unify with `Q`. The conjunct `cj` will
then be replaced with the correspondingly instantiated `P`, which may
itself be multiple conjunctions. While the goal may lose variables from
`ys` because they have been instantiated, it may also acquire new
variables from `xs`; these will be added to the goal's existential
prefix.

The new goal will be assembled to put new conjuncts first, followed by
conjuncts from the original goal in their original order (these
conjuncts may still be different if existential variables from `ys` have
been instantiated). If two conjuncts become the same because of variable
instantiation, only one will be present in the resulting goal. There is
some effort made to keep variables from the existential prefix with the
same names, but some renaming may occur, and the new goal's existential
variables will be ordered arbitrarily. If the new goal has no conjuncts,
then the tactic has proved the original.

There are four possible forms for the `pos` parameter. If it is of form
`Pos f`, `f` will be a function of type `term list -> term`, and this
function will be passed the list of conjuncts. The returned term should
be one of those conjuncts. Typical values for this function are `hd`,
`last` and `el i`, for positive integers `i`. If the `pos` parameter is
of form `Pat q`, the quotation `q` will be parsed in the context of the
goal (honouring the goal's free variables), generating a set of possible
terms (multiple terms are possible because of ambiguities caused by
overloading) that are then viewed as patterns against which the
conjuncts of the goal are matched. The first conjunct that matches the
earliest pattern in the sequence of possible parses, and which unifies
with `th`'s conclusion, is used.

The pattern form `Concl` is used to indicate that the entire goal
(including its existential prefix) should be viewed as the desired
target for `th`. This results in a call to `irule th` being made.

Finally, the pattern form `Any` is used to have the tactic search for
any conjunct that matches the conclusion (as with a pattern of
`‘_:bool’`), and if no conjunct unifies with `th`'s conclusion, to then
try to call `irule th`, as is done with the `Concl` pattern form.

### Failure

Fails if the position parameter fails to specify a term, or if that term
does not unify with the implicational theorem's conclusion. A position
may fail to specify a term in mulitple ways depending on the form of the
position. A position of form `Pos f` will fail if the function `f` fails
when applied to the goal's conjuncts. (Note that there is no failure if
`f` returns a term that is not actually a conjunct; if this term
unifies, this will simply result in new conjuncts appearing in the goal
without any old conjuncts being removed.)

A position of form `Pat q` can fail if no conjunct of the goal matches
any of the terms parsed to by `q`. The other position forms always
return at least one term to be considered. Failure after this point will
only follow if none of these terms unifies with the implicational
theorem's conclusion.

### Example

Solving a goal outright:

``` hol4
    ?- ∃x. x ≤ 3
   ============== irule_at (Pos hd) (DECIDE “y ≤ y”)
```

Refining a goal under an existential prefix (the theorem `RTC_SUBSET`
states that `∀x y. R x y ⇒ RTC R x y`):

``` hol4
    ?- ∃x y z. P x ∧ RTC R x (f y) ∧ Q y z
   ======================================== irule_at Any RTC_SUBSET
    ?- ∃z y0 x. R x (f y0) ∧ P x ∧ Q y0 z
```

Instantiating existential variables (with `LESS_MONO` stating that
`m < n ⇒ SUC m < SUC n`):

``` hol4
    ?- ∃x y z. P x ∧ SUC x < y ∧ Q y z
   ====================================== irule_at Any LESS_MONO
    ?- ∃z n m. m < n ∧ P m ∧ Q (SUC n) z
```

### Comments

The underlying operation is resolution, where one resolvent is always
the conclusion of `th`, and the other is the conjunct from the goal
selected by the position parameter. The goal is viewed as a literal
clause by negating it (via the action of `goal_assum`).

### See also

[`Tactic.irule`](#Tactic.irule),
[`Tactic.MATCH_MP_TAC`](#Tactic.MATCH_MP_TAC)
