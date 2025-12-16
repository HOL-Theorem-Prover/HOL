## `iffLR`

``` hol4
Drule.iffLR : thm -> thm
```

------------------------------------------------------------------------

Returns the left-to-right direction of a "guarded" iff theorem

A call to `iffLR th`, where `th` has the form

``` hol4
   A |- !x1 .. xn. p1 /\ .. /\ pm ==> !y... q1 /\ .. ==> ... ==> (l <=> r)
```

returns the left-to-right implication

``` hol4
   A |- !x1 .. xn. p1 /\ .. /\ pm ==> !y... q1 /\ .. ==> ... ==> l ==> r
```

The universal variables and various antecedents are said to "guard" the
if-and-only-if conclusion `l <=> r` in this situation. They may be
nested abitrarily deep, or not present at all. They are restored after a
call to `EQ_IMP_RULE` is made.

### Failure

Fails if the theorem is not of the form specified above.

### See also

[`Drule.EQ_IMP_RULE`](#Drule.EQ_IMP_RULE),
[`Drule.iffRL`](#Drule.iffRL), [`Drule.underAIs`](#Drule.underAIs)
