## `implicit_rewrites`

``` hol4
Rewrite.implicit_rewrites: unit -> rewrites
```

------------------------------------------------------------------------

Contains a number of theorems used, by default, in rewriting.

The variable `implicit_rewrites` holds a collection of rewrite rules
commonly used to simplify expressions. These rules include the clause
for reflexivity:

``` hol4
   |- !x. (x = x) = T
```

as well as rules to reason about equality:

``` hol4
   |- !t.
      ((T = t) = t) /\ ((t = T) = t) /\ ((F = t) = ~t) /\ ((t = F) = ~t)
```

Negations are manipulated by the following clauses:

``` hol4
   |- (!t. ~~t = t) /\ (~T = F) /\ (~F = T)
```

The set of tautologies includes truth tables for conjunctions,
disjunctions, and implications:

``` hol4
   |- !t.
       (T /\ t = t) /\
       (t /\ T = t) /\
       (F /\ t = F) /\
       (t /\ F = F) /\
       (t /\ t = t)
   |- !t.
       (T \/ t = T) /\
       (t \/ T = T) /\
       (F \/ t = t) /\
       (t \/ F = t) /\
       (t \/ t = t)
   |- !t.
       (T ==> t = t) /\
       (t ==> T = T) /\
       (F ==> t = T) /\
       (t ==> t = T) /\
       (t ==> F = ~t)
```

Simple rules for reasoning about conditionals are given by:

``` hol4
   |- !t1 t2. ((T => t1 | t2) = t1) /\ ((F => t1 | t2) = t2)
```

Rewriting with the following tautologies allows simplification of
universally and existentially quantified variables and abstractions:

``` hol4
   |- !t. (!x. t) = t
   |- !t. (?x. t) = t
   |- !t1 t2. (\x. t1)t2 = t1
```

The value of `implicit_rewrites` can be augmented by
`add_implicit_rewrites` and altered by `set_implicit_rewrites`.

The initial value of `implicit_rewrites` is `bool_rewrites`.

The rewrite rules held in `implicit_rewrites` are automatically included
in the simplifications performed by some of the rewriting tools.

### See also

[`Rewrite.GEN_REWRITE_RULE`](#Rewrite.GEN_REWRITE_RULE),
[`Rewrite.GEN_REWRITE_TAC`](#Rewrite.GEN_REWRITE_TAC),
[`Rewrite.REWRITE_RULE`](#Rewrite.REWRITE_RULE),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC),
[`Rewrite.bool_rewrites`](#Rewrite.bool_rewrites),
[`Rewrite.set_implicit_rewrites`](#Rewrite.set_implicit_rewrites),
[`Rewrite.add_implicit_rewrites`](#Rewrite.add_implicit_rewrites)
