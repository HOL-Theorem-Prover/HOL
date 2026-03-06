## `wlog_tac`

``` hol4
bossLib.wlog_tac : term quotation -> term quotation list -> tactic
```

------------------------------------------------------------------------

Enrich the hypotheses with a proposition that can be assumed without
loss of generality.

The user provides term quotations that parse to a proposition `P` and a
list of variables. Typically there are 2 subgoals. The first subgoal is
to prove that the general case of the original goal follows from the
specific case where `P` holds; the second subgoal is the original goal
with `P` added to the assumptions. The first subgoal is always present,
and the subgoals (if any) produced by `strip_assume_tac P |- P` follows.

If the goal is `hyp ?- t` then the first subgoal is
`hyp, !vars. ant ==> t, ~P ?- t` where `ant` is the conjunction of `P`
and those hypotheses of the original subgoal where any variable in the
user-provided list occurs free. The universal quantification is over the
variables in the user-provided list plus any variable that appears free
in `P` or `t` and is not a local constant. For convenience `~P` is
always added to the assumptions in the first subgoal because the case
for `P` follows immediately from the hypothesis. Passing a non-empty
list of variables allows to quantify over local constants in the
hypothesis `!vars. ant ==> t`.

Detailed description: Given `wlog_tac q vars_q` let `asm ?- c` be the
the goal. `q` is parsed in the goal context to a proposition `P`.
`vars_q` are parsed to variables in the goal context. Let `efv`
(effectively free variables) be the free variables of `P` and `c` that
are not free in the assumptions and are not in `vars` from left to right
and first `P`, then `c`. Let `gen_vars` be `vars @ efv`. Let `asm'` be
the elements of `asm` in which any of `vars` is a free variable. Let
`ant` be the result of splicing `p :: asm'`. The first subgoal is
`asm, (!(gen_vars). ant ==> c), ~P ?- c`. The proposition `P` is added
to the assumptions with `strip_assume_tac`. If this generates subgoals
(as is usually the case), then those subgoals follow.

A typical use case is to continue the proof assuming one case where all
cases are symmetric. The first subgoal is a good candidate to be solved
by a first order prover like `PROVE_TAC` or `METIS_TAC` providing to it
the appropriate symmetry theorems.

### Example

In the following examples assume `arithmeticTheory` is open.

``` hol4
> g(`ABS_DIFF x y + ABS_DIFF y z <= ABS_DIFF x z`);
...
> e(wlog_tac `x <= z` []);
val it =
   ABS_DIFF x y + ABS_DIFF y z <= ABS_DIFF x z
   ------------------------------------
    x <= z

   ABS_DIFF x y + ABS_DIFF y z <= ABS_DIFF x z
   ------------------------------------
     0.  !x z y. x <= z ==> ABS_DIFF x y + ABS_DIFF y z <= ABS_DIFF x z
     1.  ~(x <= z)
2 subgoals : proof
```

The first subgoal can be solved by
`prove_tac [ABS_DIFF_SYM, LESS_EQ_CASES, ADD_COMM]`.

``` hol4
> g`MAX x y <= z <=> x <= z /\ y <= z`
...
> e(wlog_tac `x <= y` []);
val it =
   MAX x y <= z <=> x <= z /\ y <= z
   ------------------------------------
    x <= y

   MAX x y <= z <=> x <= z /\ y <= z
   ------------------------------------
     0.  !x y z. x <= y ==> (MAX x y <= z <=> x <= z /\ y <= z)
     1.  ~(x <= y)
2 subgoals : proof
```

The first subgoal can be solved by
`prove_tac [LESS_EQ_CASES, MAX_COMM]`;

### Failure

Never fails.

### See also

[`bossLib.wlog_then`](#bossLib.wlog_then)
