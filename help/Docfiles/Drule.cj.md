## `cj`

``` hol4
Drule.cj : int -> thm -> thm
```

------------------------------------------------------------------------

Returns the i'th conjunct of a "guarded" theorem

A call to `cj i th`, where `th` has the form

``` hol4
   |- !x1 .. xn. p1 /\ .. /\ pm ==> !y... q1 /\ .. ==> ... ==>
                                          c1 /\ c2 /\ ... ck
```

returns the theorem

``` hol4
   |- !x1 .. xn. p1 /\ .. /\ pm ==> !y... q1 /\ .. ==> ... ==> ci
```

Note that the indexing starts at 1. The conjuncts are stripped apart
without regard to the way in which they are associated, as per the
behaviour of `CONJUNCTS`.

### Failure

Fails if the conclusion of the guarded theorem does not contain at least
`i` conjuncts. A bare term is always considered to be 1 conjunct.

### See also

[`Drule.BODY_CONJUNCTS`](#Drule.BODY_CONJUNCTS),
[`Drule.CONJUNCTS`](#Drule.CONJUNCTS),
[`Drule.underAIs`](#Drule.underAIs)
