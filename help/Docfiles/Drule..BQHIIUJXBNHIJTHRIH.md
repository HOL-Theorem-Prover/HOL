## `PART_MATCH'`

``` hol4
Drule.PART_MATCH' : (term -> term) -> thm -> term -> thm
```

------------------------------------------------------------------------

Version of `PART_MATCH` that only specialises necessary variables in
input

`PART_MATCH' selfn th tm` behaves similarly to `PART_MATCH selfn th tm`,
except that outermost, universally quantified variables in `th` are
retained in the result unless they are part of the matching.

### Failure

Fails when `PART_MATCH` would fail.

### Example

``` hol4
> IMP_DISJ_THM;
val it = ⊢ ∀A B. A ⇒ B ⇔ ¬A ∨ B: thm

> PART_MATCH (rand o lhs) IMP_DISJ_THM “p /\ A”;
val it = ⊢ A ⇒ p ∧ A ⇔ ¬A ∨ p ∧ A: thm

> PART_MATCH' (rand o lhs) IMP_DISJ_THM “p /\ A”;
val it = ⊢ ∀A'. A' ⇒ p ∧ A ⇔ ¬A' ∨ p ∧ A: thm
```

### See also

[`Drule.PART_MATCH`](#Drule.PART_MATCH)
