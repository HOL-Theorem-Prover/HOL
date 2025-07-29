## `MATCH_ACCEPT_TAC`

``` hol4
Tactic.MATCH_ACCEPT_TAC : thm_tactic
```

------------------------------------------------------------------------

Solves a goal which is an instance of the supplied theorem.

When given a theorem `A' |- t` and a goal `A ?- t'` where `t` can be
matched to `t'` by instantiating variables which are either free or
universally quantified at the outer level, including appropriate type
instantiation, `MATCH_ACCEPT_TAC` completely solves the goal.

``` hol4
    A ?- t'
   =========  MATCH_ACCEPT_TAC (A' |- t)
```

Unless `A'` is a subset of `A`, this is an invalid tactic.

### Failure

Fails unless the theorem has a conclusion which is instantiable to match
that of the goal.

### Example

The following example shows variable and type instantiation at work. We
can use the polymorphic list theorem `HD`:

``` hol4
   HD = |- !h t. HD(CONS h t) = h
```

to solve the goal:

``` hol4
   ?- HD [1;2] = 1
```

simply by:

``` hol4
   MATCH_ACCEPT_TAC HD
```

### Comments

`prim_irule` is similar, with differences in the details

### See also

[`Tactic.ACCEPT_TAC`](#Tactic.ACCEPT_TAC),
[`Tactic.prim_irule`](#Tactic.prim_irule)
