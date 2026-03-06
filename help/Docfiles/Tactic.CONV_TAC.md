## `CONV_TAC`

``` hol4
Tactic.CONV_TAC : (conv -> tactic)
```

------------------------------------------------------------------------

Makes a tactic from a conversion.

If `c` is a conversion, then `CONV_TAC c` is a tactic that applies `c`
to the goal. That is, if `c` maps a term `"g"` to the theorem
`|- g = g'`, then the tactic `CONV_TAC c` reduces a goal `g` to the
subgoal `g'`. More precisely, if `c "g"` returns `A' |- g = g'`, then:

``` hol4
         A ?- g
     ===============  CONV_TAC c
         A ?- g'
```

If `c` raises `UNCHANGED` then `CONV_TAC c` reduces a goal to itself.

Note that the conversion `c` should return a theorem whose assumptions
are also among the assumptions of the goal (normally, the conversion
will returns a theorem with no assumptions). `CONV_TAC` does not fail if
this is not the case, but the resulting tactic will be invalid, so the
theorem ultimately proved using this tactic will have more assumptions
than those of the original goal.

### Failure

`CONV_TAC c` applied to a goal `A ?- g` fails if `c` fails (other than
by raising `UNCHANGED`) when applied to the term `g`. The function
returned by `CONV_TAC c` will also fail if the ML function `c:term->thm`
is not, in fact, a conversion (i.e. a function that maps a term `t` to a
theorem `|- t = t'`).

`CONV_TAC` is used to apply simplifications that can't be expressed as
equations (rewrite rules). For example, a goal can be simplified by
beta-reduction, which is not expressible as a single equation, using the
tactic

``` hol4
   CONV_TAC(DEPTH_CONV BETA_CONV)
```

The conversion `BETA_CONV` maps a beta-redex `"(\x.u)v"` to the theorem

``` hol4
   |- (\x.u)v = u[v/x]
```

and the ML expression `(DEPTH_CONV BETA_CONV)` evaluates to a conversion
that maps a term `"t"` to the theorem `|- t=t'` where `t'` is obtained
from `t` by beta-reducing all beta-redexes in `t`. Thus
`CONV_TAC(DEPTH_CONV BETA_CONV)` is a tactic which reduces beta-redexes
anywhere in a goal.

### See also

[`Abbrev.conv`](#Abbrev.conv), [`Conv.UNCHANGED`](#Conv.UNCHANGED),
[`Conv.CONV_RULE`](#Conv.CONV_RULE)
