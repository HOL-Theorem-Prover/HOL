## `FILTER_STRIP_TAC`

``` hol4
Tactic.FILTER_STRIP_TAC : term -> tactic
```

------------------------------------------------------------------------

Conditionally strips apart a goal by eliminating the outermost
connective.

Stripping apart a goal in a more careful way than is done by `STRIP_TAC`
may be necessary when dealing with quantified terms and implications.
`FILTER_STRIP_TAC` behaves like `STRIP_TAC`, but it does not strip apart
a goal if it contains a given term.

If `u` is a term, then `FILTER_STRIP_TAC u` is a tactic that removes one
outermost occurrence of one of the connectives `!`, `==>`, `~` or `/\`
from the conclusion of the goal `t`, provided the term being stripped
does not contain `u`. A negation `~t` is treated as the implication
`t ==> F`. `FILTER_STRIP_TAC u` also breaks apart conjunctions without
applying any filtering.

If `t` is a universally quantified term, `FILTER_STRIP_TAC u` strips off
the quantifier:

``` hol4
      A ?- !x.v
   ================  FILTER_STRIP_TAC ``u``       [where x is not u]
     A ?- v[x'/x]
```

where `x'` is a primed variant that does not appear free in the
assumptions `A`. If `t` is a conjunction, no filtering is done and
`FILTER_STRIP_TAC u` simply splits the conjunction:

``` hol4
      A ?- v /\ w
   =================  FILTER_STRIP_TAC ``u``
    A ?- v   A ?- w
```

If `t` is an implication and the antecedent does not contain a free
instance of `u`, then `FILTER_STRIP_TAC u` moves the antecedent into the
assumptions and recursively splits the antecedent according to the
following rules (see `STRIP_ASSUME_TAC`):

``` hol4
    A ?- v1 /\ ... /\ vn ==> v            A ?- v1 \/ ... \/ vn ==> v
   ============================        =================================
       A u {v1,...,vn} ?- v             A u {v1} ?- v ... A u {vn} ?- v

     A ?- ?x.w ==> v
   ====================
    A u {w[x'/x]} ?- v
```

where `x'` is a variant of `x`.

### Failure

`FILTER_STRIP_TAC u (A,t)` fails if `t` is not a universally quantified
term, an implication, a negation or a conjunction; or if the term being
stripped contains `u` in the sense described above (conjunction
excluded).

### Example

When trying to solve the goal

``` hol4
   ?- !n. m <= n /\ n <= m ==> (m = n)
```

the universally quantified variable `n` can be stripped off by using

``` hol4
   FILTER_STRIP_TAC ``m:num``
```

and then the implication can be stripped apart by using

``` hol4
   FILTER_STRIP_TAC ``m:num = n``
```

`FILTER_STRIP_TAC` is used when stripping outer connectives from a goal
in a more delicate way than `STRIP_TAC`. A typical application is to
keep stripping by using the tactic `REPEAT (FILTER_STRIP_TAC u)` until
one hits the term `u` at which stripping is to stop.

### See also

[`Tactic.CONJ_TAC`](#Tactic.CONJ_TAC),
[`Tactic.FILTER_DISCH_TAC`](#Tactic.FILTER_DISCH_TAC),
[`Tactic.FILTER_DISCH_THEN`](#Tactic.FILTER_DISCH_THEN),
[`Tactic.FILTER_GEN_TAC`](#Tactic.FILTER_GEN_TAC),
[`Tactic.STRIP_ASSUME_TAC`](#Tactic.STRIP_ASSUME_TAC),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC)
