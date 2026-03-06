## `suffices_by`

``` hol4
op bossLib.suffices_by : term quotation * tactic -> tactic
```

------------------------------------------------------------------------

Replace the goal's conclusion with a sufficient alternative.

A call to the tactic `q suffices_by tac` will first attempt to parse the
quotation `q` in the context of the current goal. Assuming this
generates a term `qt` of boolean type, it will then generate two
sub-goals. Assuming the current goal is `asl ?- g`, the first new
sub-goal will be that `qt` implies `g`, thus `asl ?- qt ==> g`. The
second goal will be `asl ?- qt`.

The system next applies `tac` to the first sub-goal (the implication).
If `tac` solves the goal (the common or at least, desired, case), the
user will then be presented with one goal, where the original `g` has
been replaced with `qt`. In this way, the user has adjusted the goal,
replacing the old `g` with a `qt` that is sufficient to prove it.

### Failure

A call to `q suffices_by tac` will fail if the quotation `q` does not
parse to a term of boolean type. This parsing is done in the context of
the whole goal `(asl,g)`, using the `parse_in_context` function. The
call will also fail if `tac` does not solve the newly generated subgoal.

### Example

If the current goal is

``` hol4
   f n m = f m n
   ------------------------------------
     0.  m <= n
     1.  n <= m
```

then the tactic `` `m = n` suffices_by SIMP_TAC bool_ss [] `` will
result in the goal

``` hol4
   m = n
   ------------------------------------
     0.  m <= n
     1.  n <= m
```

where the call to `SIMP_TAC` has successfully proved the theorem

``` hol4
   |- (m = n) ==> (f m n = f n m)
```

eliminating the first of the two sub-goals that was generated.

### Comments

The tactic `suffices_by` is designed to support a backwards style of
reasoning. Superficially, it appears to be dual to the tactic `by`,
which provides a forward-reasoning facility. In fact, both are
implementing a backwards application of the sequent calculus's "cut"
rule; the difference is which of the two premises to the rule is worked
on by the provided tactics.

### See also

[`bossLib.by`](#bossLib.by),
[`Parse.parse_in_context`](#Parse.parse_in_context),
[`Tactic.SUFF_TAC`](#Tactic.SUFF_TAC)
