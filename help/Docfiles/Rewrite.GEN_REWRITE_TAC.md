## `GEN_REWRITE_TAC`

``` hol4
Rewrite.GEN_REWRITE_TAC : ((conv -> conv) -> rewrites -> thm list -> tactic)
```

------------------------------------------------------------------------

Rewrites a goal, selecting terms according to a user-specified strategy.

Distinct rewriting tactics differ in the search strategies used in
finding subterms on which to apply substitutions, and the built-in
theorems used in rewriting. In the case of `REWRITE_TAC`, this is a
recursive traversal starting from the body of the goal's conclusion
part, while in the case of `ONCE_REWRITE_TAC`, for example, the search
stops as soon as a term on which a substitution is possible is found.
`GEN_REWRITE_TAC` allows a user to specify a more complex strategy for
rewriting.

The basis of pattern-matching for rewriting is the notion of
conversions, through the application of `REWR_CONV`. Conversions are
rules for mapping terms with theorems equating the given terms to other
semantically equivalent ones.

When attempting to rewrite subterms recursively, the use of conversions
(and therefore rewrites) can be automated further by using functions
which take a conversion and search for instances at which they are
applicable. Examples of these functions are `ONCE_DEPTH_CONV` and
`RAND_CONV`. The first argument to `GEN_REWRITE_TAC` is such a function,
which specifies a search strategy; i.e. it specifies how subterms (on
which substitutions are allowed) should be searched for.

The second and third arguments are lists of theorems used for rewriting.
The order in which these are used is not specified. The theorems need
not be in equational form: negated terms, say `"~ t"`, are transformed
into the equivalent equational form `"t = F"`, while other
non-equational theorems with conclusion of form `"t"` are cast as the
corresponding equations `"t = T"`. Conjunctions are separated into the
individual components, which are used as distinct rewrites.

### Failure

`GEN_REWRITE_TAC` fails if the search strategy fails. It may also cause
a non-terminating sequence of rewrites, depending on the search strategy
used. The resulting tactic is invalid when a theorem which matches the
goal (and which is thus used for rewriting it with) has a hypothesis
which is not alpha-convertible to any of the assumptions of the goal.
Applying such an invalid tactic may result in a proof of a theorem which
does not correspond to the original goal.

Detailed control of rewriting strategy, allowing a user to specify a
search strategy.

### Example

Given a goal such as:

``` hol4
   ?- a - (b + c) = a - (c + b)
```

we may want to rewrite only one side of it with a theorem, say
`ADD_SYM`. Rewriting tactics which operate recursively result in
divergence; the tactic `ONCE_REWRITE_TAC [ADD_SYM]` rewrites on both
sides to produce the following goal:

``` hol4
   ?- a - (c + b) = a - (b + c)
```

as `ADD_SYM` matches at two positions. To rewrite on only one side of
the equation, the following tactic can be used:

``` hol4
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [ADD_SYM]
```

which produces the desired goal:

``` hol4
   ?- a - (c + b) = a - (c + b)
```

As another example, one can write a tactic which will behave similarly
to `REWRITE_TAC` but will also include `ADD_CLAUSES` in the set of
theorems to use always:

``` hol4
   val ADD_REWRITE_TAC = GEN_REWRITE_TAC TOP_DEPTH_CONV
                             (add_rewrites (implicit_rewrites ())
                                           [ADD_CLAUSES])
```

### See also

[`Rewrite.ASM_REWRITE_TAC`](#Rewrite.ASM_REWRITE_TAC),
[`Rewrite.GEN_REWRITE_RULE`](#Rewrite.GEN_REWRITE_RULE),
[`Rewrite.ONCE_REWRITE_TAC`](#Rewrite.ONCE_REWRITE_TAC),
[`Rewrite.PURE_REWRITE_TAC`](#Rewrite.PURE_REWRITE_TAC),
[`Conv.REWR_CONV`](#Conv.REWR_CONV),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC)
