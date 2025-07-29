## `CONG_TAC`

``` hol4
bossLib.CONG_TAC : int option -> tactic
```

------------------------------------------------------------------------

Applies congruence rules backwards repeatedly to attack an equality

Applying `CONG_TAC dopt` to a goal `?- x = y` attempts to apply
congruence rules backwards repeatedly, generating a number of further
equality subgoals. The `dopt` parameter limits the number of times this
will be done: when `dopt` is `NONE`, there is no limit: the base
transformation will be tried on the initial and all subsequent goals. If
`dopt` is `SOME i`, then `i` is the total number of transformations that
will be made. (If `dopt` is `SOME 0` then `CONG_TAC dopt` is equivalent
to `ALL_TAC`.)

If at least one of the equality's arguments is an abstraction (possibly
paired), then the transformation rewrites with function extensionality,
strips the universally quantified variables, and beta-reduces where
necessary.

If at least one of the equality's arguments is a set comprehension, then
the transformation rewrites with set-extensionality and applies the
conversion that calculates what it is for a term to be a member of a
comprehension to one or both sides of the equality. Unless both sides
are set comprehensions, this is likely to be the last transformation
possible.

If the goal matches the conclusion of any of the theorems stored as
congruences for the definition package (with attribute name `defncong`
or `cong`), then this theorem is applied backwards to generate new
sub-goals. If the new sub-goals include preconditions and universally
quantified variables, these are stripped into the assumptions.

Finally, the "base transformation" depends on the shape of the
equality's arguments. If both sides are combinations (`M e1` and `N e2`,
say), then the base transformation will be similar to an application of
`MK_COMB_TAC`, generating at least the goals `?- M = N` and
`?- e1 = e2`. When the head terms of both applications are equal, then
one step of the base transformation is taken to be the iteration of
`MK_COMB_TAC` that strips all arguments, so that
`?- f e1 .. en = f e1' .. en'` will turn into `n` subgoals, each of the
form `?- ei = ei'`. (The `?- f = f` subgoal will be eliminated
immediately, as below.)

In all cases, new subgoals that are instances of reflexivity, or which
occur in the goal's assumptions (with either orientation) are
immediately eliminated.

### Failure

Fails if the provided depth is either `NONE` or `SOME i` with `i`
greater than zero, and the goal is not an equality at all, or cannot be
changed by any of the transformations described above. For example, with
`f : 'a -> num` and `g : num -> num`, the goal `?- f a = g n` cannot be
reduced.

### Example

The following involves a handling of abstractions:

``` hol4
   > CONG_TAC NONE ([], “(∀x. f (z:'a) < x) ⇔ (∀y. c < y)”);
   val it = ([([], “f z = c”)], fn): goal list * validation
```

Slightly altering the goal, and keeping the depth as `NONE` turns
something true into something unprovable:

``` hol4
   > CONG_TAC NONE ([], “(∀x. f (z:'a) < x) ⇔ (∀y. y < 6)”);
   val it = ([([], “f z = x”), ([], “x = 6”)], fn): goal list * validation
```

where the `x` in each sub-goal is completely fresh.

Finally, user-congruences can give richer contexts when proving
functions equal:

``` hol4
   > CONG_TAC NONE 
       ([], “MAP (λa. f a + 1) (l1:'a list) = MAP g (l2:'a list)”);
   val it = ([([“MEM x l2”], “f x + 1 = g x”), ([], “l1 = l2”)], fn):
      goal list * validation
```

### Comments

This is a powerful tool for taking apart two terms that share a skeleton
and need only have their leaves shown to be equal. Equally, it is quite
possible for this tactic to turn a solvable goal into an unsolvable one.

An application of `CONG_TAC` will never break apart the function
applications that lie within the representation of natural number
numerals.

The name `cong_tac` can be used as an alias for `CONG_TAC`.

### See also

[`Tactic.AP_TERM_TAC`](#Tactic.AP_TERM_TAC),
[`Tactic.AP_THM_TAC`](#Tactic.AP_THM_TAC),
[`Tactic.MK_COMB_TAC`](#Tactic.MK_COMB_TAC)
