## `COND_REWR_TAC`

``` hol4
Cond_rewrite.COND_REWR_TAC :
 (term -> term -> ((term * term) list * (type * type) list) list) ->
 thm_tactic
```

------------------------------------------------------------------------

A lower level tactic used to implement simple conditional rewriting
tactic.

`COND_REWR_TAC` is one of the basic building blocks for the
implementation of conditional rewriting in the HOL system. In
particular, the conditional term replacement or rewriting done by all
the built-in conditional rewriting tactics is ultimately done by
applications of `COND_REWR_TAC`. The description given here for
`COND_REWR_TAC` may therefore be taken as a specification of the atomic
action of replacing equals by equals in the goal under certain
conditions that aare used in all these higher level conditional
rewriting tactics.

The first argument to `COND_REWR_TAC` is expected to be a function which
returns a list of matches. Each of these matches is in the form of the
value returned by the built-in function `match`. It is used to search
the goal for instances which may be rewritten.

The second argument to `COND_REWR_TAC` is expected to be an implicative
theorem in the following form:

``` hol4
   A |- !x1 ... xn. P1 ==> ... Pm ==> (Q[x1,...,xn] = R[x1,...,xn])
```

where `x1`, ..., `xn` are all the variables that occur free in the
left-hand side of the conclusion of the theorem but do not occur free in
the assumptions.

If `fn` is a function and `th` is an implicative theorem of the kind
shown above, then `COND_REWR_TAC fn th` will be a tactic which returns a
list of subgoals if evaluating

``` hol4
   fn Q[x1,...,xn] gl
```

returns a non-empty list of matches when applied to a goal `(asm,gl)`.

Let `ml` be the match list returned by evaluating `fn Q[x1,...,xn] gl`.
Each element in this list is in the form of

``` hol4
   ([(e1,x1);...;(ep,xp)], [(ty1,vty1);...;(tyq,vtyq)])
```

which specifies the term and type instantiations of the input theorem
`th`. Either the term pair list or the type pair list may be empty. In
the case that both lists are empty, an exact match is found, i.e., no
instantiation is required. If `ml` is an empty list, no match has been
found and the tactic will fail.

For each match in `ml`, `COND_REWR_TAC` will perform the following: 1)
instantiate the input theorem `th` to get

``` hol4
   th' = A |- P1' ==> ... ==> Pm' ==> (Q' = R')
```

where the primed subterms are instances of the corresponding unprimed
subterms obtained by applying `INST_TYPE` with
`[(ty1,vty1);...;(tyq,vtyq)]` and then `INST` with
`[(e1,x1);...;(ep,xp)]`; 2) search the assumption list `asm` for
occurrences of any antecedents `P1'`, ..., `Pm'`; 3) if all antecedents
appear in `asm`, the goal `gl` is reduced to `gl'` by substituting `R'`
for each free occurrence of `Q'`, otherwise, in addition to the
substitution, all antecedents which do not appear in `asm` are added to
it and new subgoals corresponding to these antecedents are created. For
example, if `Pk'`, ..., `Pm'` do not appear in `asm`, the following
subgoals are returned:

``` hol4
   asm ?- Pk'  ...  asm ?- Pm'   {{asm,Pk',...,Pm'}} ?- gl'
```

If `COND_REWR_TAC` is given a theorem `th`:

``` hol4
   A |- !x1 ... xn y1 ... yk. P1 ==> ... ==> Pm ==> (Q = R)
```

where the variables `y1`, ..., `ym` do not occur free in the left-hand
side of the conclusion `Q` but they do occur free in the antecedents,
then, when carrying out Step 2 described above, `COND_REWR_TAC` will
attempt to find instantiations for these variables from the assumption
`asm`. For example, if `x1` and `y1` occur free in `P1`, and a match is
found in which `e1` is an instantiation of `x1`, then `P1'` will become
`P1[e1/x1, y1]`. If a term `P1'' = P1[e1,e1'/x1,y1]` appears in `asm`,
`th'` is instantiated with `(e1', y1)` to get

``` hol4
   th'' = A |- P1'' ==> ... ==> Pm'' ==> (Q' = R'')
```

then `R''` is substituted into `gl` for all free occurrences of `Q'`. If
no consistent instantiation is found, then `P1'` which contains the
uninstantiated variable `y1` will become one of the new subgoals. In
such a case, the user has no control over the choice of the variable
`yi`.

### Failure

`COND_REWR_TAC fn th` fails if `th` is not an implication of the form
described above. If `th` is such an equation, but the function `fn`
returns a null list of matches, or the function `fn` returns a non-empty
list of matches, but the term or type instantiation fails.

### Example

The following example illustrates a straightforward use of
`COND_REWR_TAC`. We use the built-in theorem `LESS_MOD` as the input
theorem, and the function `search_top_down` as the search function.

``` hol4
   #LESS_MOD;;
   Theorem LESS_MOD autoloading from theory `arithmetic` ...
   LESS_MOD = |- !n k. k < n ==> (k MOD n = k)

   |- !n k. k < n ==> (k MOD n = k)

   #search_top_down;;
   - : (term -> term -> ((term # term) list # (type # type) list) list)
```

We set up a goal

``` hol4
   #g"2 MOD 3 = 2";;
   "2 MOD 3 = 2"

   () : void
```

and then apply the tactic

``` hol4
   #e(COND_REWR_TAC search_top_down LESS_MOD);;
   OK..
   2 subgoals
   "2 = 2"
       [ "2 < 3" ]

   "2 < 3"

    () : void
```

### See also

[`Cond_rewrite.COND_REWRITE1_TAC`](#Cond_rewrite.COND_REWRITE1_TAC),
[`Cond_rewrite.COND_REWRITE1_CONV`](#Cond_rewrite.COND_REWRITE1_CONV),
[`Cond_rewrite.COND_REWR_CONV`](#Cond_rewrite.COND_REWR_CONV),
[`Cond_rewrite.COND_REWR_CANON`](#Cond_rewrite.COND_REWR_CANON),
[`Cond_rewrite.search_top_down`](#Cond_rewrite.search_top_down)
