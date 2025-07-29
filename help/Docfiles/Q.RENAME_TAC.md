## `RENAME_TAC`

``` hol4
Q.RENAME_TAC : term quotation list -> tactic
```

------------------------------------------------------------------------

Renames free variables or subterms within a goal.

A call to `RENAME_TAC qs` searches the current goal for matches to the
patterns in the list `qs`, and then substitutes out the matches (in the
"reverse direction") so that the goal becomes one that uses the names
from `qs`. This can cause subterms within the goal to turn into simple
variables, but the usual intention is to rename free variables into the
variables that appear in the patterns.

The matching is done without reference to the goal's existing free
variables. If a variable in `qs` clashes with an existing variable in
the goal, then the goal's variable will be renamed away. It is
sufficient for variables to have the same name to "clash"; they need not
also have the same type. The search for matches begins by attempting to
find matches against the whole of the goal, against whole assumptions,
for sub-terms within the goal, and then sub-terms of assumptions.

These four different flavours of searching can additionally be
controlled by adding comments `(* ... *)` to the end of the relevant
quotation. The string in the comment has its whitespace stripped, and is
then split into fields using the pipe character `|` as a separator. If
the string consisting of the single character `g` is present, the
pattern is checked against the entirety of the goal's conclusion; the
string of character `a` causes a check against each individual
assumption; the strings `sg` and `sa` cause checks against sub-terms
present in the conclusion, or in any assumption respectively.

If multiple matches are possible, a variant tactic, `Q.kRENAME_TAC`, can
be used: this tactic takes an additional "continuation" tactic argument
that can be used to discriminate between these matches.

Patterns can use underscores to match anything without any change in the
goal's naming being introduced. Underscores can match against sub-terms
that include bound variables. Matching is first-order.

### Failure

Fails if it is impossible to consistently match the combination of
patterns in the provided list of quotations (`qs`).

### Example

If the goal is of the form

``` hol4
   x < y, y < z ?- x < f a
```

then invoking `` Q.RENAME_TAC [`b < c`, `a < b`] `` will produce the
sub-goal:

``` hol4
   a < b, b < c ?- a < f a'
```

where the goal's original `a` variable (which is not even of type
`num`), has been renamed away from `a` because that variable occurs in
the patterns. (If the right hand side of the inequality was simply `a`
and was thus of type num, it would also be renamed to `a'`.)

If `` Q.RENAME_TAC [`b < c`] `` is invoked on the same initial goal, the
result is:

``` hol4
   b < y, y < z ?- b < c
```

illustrating the way in which variables can eliminate more complicated
sub-terms.

The useful way in which underscores in patterns can be used to "dodge"
terms including bound variables is illustrated in the next example,
where the initial goal is:

``` hol4
   (!a. f a < z), z < c ?- z < d
```

After applying `` Q.RENAME_TAC [`_ < x`, `x < c`] ``, the goal becomes

``` hol4
   (!a. f a < x), x < c' ?- x < c
```

The goal was chosen for the match to the second pattern because the goal
is considered first. If the initial goal had been

``` hol4
   (!a. f a < z), z < c ?- z < d /\ P z
```

then the result of the same application would be

``` hol4
   (!a. f a < z), z < c ?- x < d /\ P x
```

because whole assumptions are considered before sub-terms of the goal.

The pattern-specification comments can be important when selecting for
certain assumptions. Here, `Q.RENAME_TAC [‘x < _ (* a *)’]` will fail
because there is no assumption of the required shape, even though the
shape appears as a subterm in the assumptions, and is the shape of the
goal's conclusion:

``` hol4
   ~(a < b) ?- c < d
```

Similarly, using the comment `(* a|sg *)` would also fail because the
pattern is not present as a sub-term of the goal's conclusion.

### Comments

This function is also available under the name `bossLib.rename`.

Note that `Q.RENAME_TAC [q]` is *not* the same as `Q.RENAME1_TAC q`. The
latter pays attention to the goal's free variables, using these to
constrain the match to the pattern. In contrast, `Q.RENAME_TAC`
completely ignores all of the goal's free variables, such that using an
existing name in a pattern doesn't make any difference to the matching
behaviour.

### See also

[`Q.RENAME1_TAC`](#Q.RENAME1_TAC)
