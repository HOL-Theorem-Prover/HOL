## `ABBREV_TAC`

``` hol4
Q.ABBREV_TAC : term quotation -> tactic
```

------------------------------------------------------------------------

Introduces an abbreviation into a goal.

The tactic `Q.ABBREV_TAC q` parses the quotation `q` in the context of
the goal to which it is applied. The result must be a term of the form
`v = e` with `v` a variable. The effect of the tactic is to replace the
term `e` wherever it occurs in the goal by `v` (or a primed variant of
`v` if `v` already occurs in the goal), and to add the assumption
`Abbrev(v = e)` to the goal's assumptions. Again, if `v` already occurs
free in the goal, then the new assumption will be `Abbrev(v' = e)`, with
`v'` a suitably primed version of `v`.

It is not an error if the expression `e` does not occur anywhere within
the goal. In this situation, the effect of the tactic is simply to add
the assumption `Abbrev(v = e)`.

The `Abbrev` constant is defined in `markerTheory` to be the identity
function over boolean values. It is used solely as a tag, so that
abbreviations can be found by other tools, and so that simplification
tactics such as `RW_TAC` will not eliminate them. When it sees them as
part of its context, the simplifier treats terms of the form
`Abbrev(v = e)` as assumptions `e = v`. In this way, the simplifier can
use abbreviations to create further sharing, after an abbreviation's
creation.

Abbreviation assumptions of this form "protect" their variable argument;
simplification tactics (e.g., `fs`) will not replace the variable `v`,
even though they may have been passed rewrites to use such as `v = e'`.

### Failure

Fails if the quotation is ill-typed. This may happen because variables
in the quotation that also appear in the goal are given the same type in
the quotation as they have in the goal. Also fails if the variable of
the equation appears in the expression that it is supposed to be
abbreviating.

### Example

Substitution in the goal:

``` hol4
   > Q.ABBREV_TAC ‘n = 10’ ([], “10 < 9 * 10”);
   val it = ([([“Abbrev(n = 10)”], “n < 9 * n”)], fn) :
     (term list * term) list * (thm list -> thm)
```

and the assumptions:

``` hol4
   > Q.ABBREV_TAC ‘m = n + 2’ ([“f (n + 2) < 6”], “n < 7”);
   val it = ([([“Abbrev(m = n + 2)”, “f m < 6”], “n < 7”)], fn) :
     (term list * term) list * (thm list -> thm)
```

and both

``` hol4
   > Q.ABBREV_TAC ‘u = x ** 32’ ([“x ** 32 = f z”],
                                  “g (x ** 32 + 6) - 10 < 65”);
   val it =
       ([([“Abbrev(u = x ** 32)”, “u = f z”], “g (u + 6) - 10 < 65”)],
        fn) :
       (term list * term) list * (thm list -> thm)
```

### Comments

The `bossLib` library provides `qabbrev_tac` as a synonym for
`Q.ABBREV_TAC`.

It is possible to abbreviate functions, using quotations such as
`‘f = \n. n + 3’`. When this is done `ABBREV_TAC` will not itself do
anything more than replace exact copies of the abstraction, but the
simplifier will subsequently see occurrences of the pattern and replace
them.

Thus:

``` hol4
   > (qabbrev_tac ‘f = \x. x + 1’ >> asm_simp_tac bool_ss [])
        ([], “3 + 1 = 4 + 1”);
   val it =
      ([([“Abbrev (f = (\x. x + 1))”], “f 3 = f 4”)], fn):
      goal list * (thm list -> thm)
```

where the simplifier has seen occurrences of the `x+1` pattern and
replaced it with calls to the `f`-abbreviation.

### See also

[`BasicProvers.Abbr`](#BasicProvers.Abbr),
[`Q.HO_MATCH_ABBREV_TAC`](#Q.HO_MATCH_ABBREV_TAC),
[`Q.MATCH_ABBREV_TAC`](#Q.MATCH_ABBREV_TAC),
[`Q.UNABBREV_TAC`](#Q.UNABBREV_TAC)
