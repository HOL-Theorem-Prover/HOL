## `REWRITE_TAC`

``` hol4
Rewrite.REWRITE_TAC : (thm list -> tactic)
```

------------------------------------------------------------------------

Rewrites a goal including built-in tautologies in the list of rewrites.

Rewriting tactics in HOL provide a recursive left-to-right matching and
rewriting facility that automatically decomposes subgoals and justifies
segments of proof in which equational theorems are used, singly or
collectively. These include the unfolding of definitions, and the
substitution of equals for equals. Rewriting is used either to advance
or to complete the decomposition of subgoals.

`REWRITE_TAC` transforms (or solves) a goal by using as rewrite rules
(i.e. as left-to-right replacement rules) the conclusions of the given
list of (equational) theorems, as well as a set of built-in theorems
(common tautologies) held in the ML variable `implicit_rewrites`.
Recognition of a tautology often terminates the subgoaling process
(i.e. solves the goal).

The equational rewrites generated are applied recursively and to
arbitrary depth, with matching and instantiation of variables and type
variables. A list of rewrites can set off an infinite rewriting process,
and it is not, of course, decidable in general whether a rewrite set has
that property. The order in which the rewrite theorems are applied is
unspecified, and the user should not depend on any ordering.

See `GEN_REWRITE_TAC` for more details on the rewriting process.
Variants of `REWRITE_TAC` allow the use of a different set of rewrites.
Some of them, such as `PURE_REWRITE_TAC`, exclude the basic tautologies
from the possible transformations. `ASM_REWRITE_TAC` and others include
the assumptions at the goal in the set of possible rewrites.

Still other tactics allow greater control over the search for rewritable
subterms. Several of them such as `ONCE_REWRITE_TAC` do not apply
rewrites recursively. `GEN_REWRITE_TAC` allows a rewrite to be applied
at a particular subterm.

### Failure

`REWRITE_TAC` does not fail. Certain sets of rewriting theorems on
certain goals may cause a non-terminating sequence of rewrites.
Divergent rewriting behaviour results from a term `t` being immediately
or eventually rewritten to a term containing `t` as a sub-term. The
exact behaviour depends on the `HOL` implementation.

### Example

The arithmetic theorem `GREATER_DEF`, `|- !m n. m > n = n < m`, is used
below to advance a goal:

``` hol4
   - REWRITE_TAC [GREATER_DEF] ([],``5 > 4``);
   > ([([], ``4 < 5``)], -) : subgoals
```

It is used below with the theorem `LESS_0`, `|- !n. 0 < (SUC n)`, to
solve a goal:

``` hol4
   - val (gl,p) =
       REWRITE_TAC [GREATER_DEF, LESS_0] ([],``(SUC n) > 0``);
   > val gl = [] : goal list
   > val p = fn : proof

   - p[];
   > val it = |- (SUC n) > 0 : thm
```

Rewriting is a powerful and general mechanism in HOL, and an important
part of many proofs. It relieves the user of the burden of directing and
justifying a large number of minor proof steps. `REWRITE_TAC` fits a
forward proof sequence smoothly into the general goal-oriented
framework. That is, (within one subgoaling step) it produces and
justifies certain forward inferences, none of which are necessarily on a
direct path to the desired goal.

`REWRITE_TAC` may be more powerful a tactic than is needed in certain
situations; if efficiency is at stake, alternatives might be considered.
On the other hand, if more power is required, the simplification
functions (`SIMP_TAC` and others) may be appropriate.

### See also

[`Rewrite.ASM_REWRITE_TAC`](#Rewrite.ASM_REWRITE_TAC),
[`Rewrite.GEN_REWRITE_TAC`](#Rewrite.GEN_REWRITE_TAC),
[`Rewrite.FILTER_ASM_REWRITE_TAC`](#Rewrite.FILTER_ASM_REWRITE_TAC),
[`Rewrite.FILTER_ONCE_ASM_REWRITE_TAC`](#Rewrite.FILTER_ONCE_ASM_REWRITE_TAC),
[`Rewrite.ONCE_ASM_REWRITE_TAC`](#Rewrite.ONCE_ASM_REWRITE_TAC),
[`Rewrite.ONCE_REWRITE_TAC`](#Rewrite.ONCE_REWRITE_TAC),
[`Rewrite.PURE_ASM_REWRITE_TAC`](#Rewrite.PURE_ASM_REWRITE_TAC),
[`Rewrite.PURE_ONCE_ASM_REWRITE_TAC`](#Rewrite.PURE_ONCE_ASM_REWRITE_TAC),
[`Rewrite.PURE_ONCE_REWRITE_TAC`](#Rewrite.PURE_ONCE_REWRITE_TAC),
[`Rewrite.PURE_REWRITE_TAC`](#Rewrite.PURE_REWRITE_TAC),
[`Conv.REWR_CONV`](#Conv.REWR_CONV),
[`Rewrite.REWRITE_CONV`](#Rewrite.REWRITE_CONV),
[`simpLib.SIMP_TAC`](#simpLib.SIMP_TAC),
[`Tactic.SUBST_TAC`](#Tactic.SUBST_TAC)
