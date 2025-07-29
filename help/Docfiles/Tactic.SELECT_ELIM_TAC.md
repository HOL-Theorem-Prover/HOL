## `SELECT_ELIM_TAC`

``` hol4
Tactic.SELECT_ELIM_TAC : tactic
```

------------------------------------------------------------------------

Eliminates a Hilbert-choice ("selection") term from the goal.

`SELECT_ELIM_TAC` searches the goal it is applied to for terms involving
the Hilbert-choice operator, of the form `@x. ...`. If such a term is
found, then the tactic will produce a new goal, where the choice term
has disappeared. The resulting goal will require the proof of the
non-emptiness of the choice term's predicate, and that any possible
choice of value from that predicate will satisfy the original goal.

Thus, `SELECT_ELIM_TAC` can be seen as a higher-order match against the
theorem

``` hol4
   |- !P Q. (?x. P x) /\ (!x. P x ==> Q x) ==> Q ($@ P)
```

where the new goal is the antecedent of the implication. (This theorem
is `SELECT_ELIM_THM`, from theory `bool`.)

### Example

When applied to this goal,

``` hol4
   - SELECT_ELIM_TAC ([], ``(@x. x < 4) < 5``);
   > val it = ([([], ``(?x. x < 4) /\ !x. x < 4 ==> x < 5``)], fn) :
       (term list * term) list * (thm list -> thm)
```

the resulting goal requires the proof of the existence of a number less
than 4, and also that any such number is also less than 5.

### Failure

Fails if there are no choice terms in the goal.

### Comments

If the choice-term's predicate is everywhere false, goals involving such
terms will be true only if the choice of term makes no difference at
all. Such situations can be handled with the use of `SPEC_TAC`. Note
also that the choice of select term to eliminate is made in an
unspecified manner.

### See also

[`Tactic.DEEP_INTRO_TAC`](#Tactic.DEEP_INTRO_TAC),
[`Drule.SELECT_ELIM`](#Drule.SELECT_ELIM),
[`Drule.SELECT_INTRO`](#Drule.SELECT_INTRO),
[`Drule.SELECT_RULE`](#Drule.SELECT_RULE),
[`Tactic.SPEC_TAC`](#Tactic.SPEC_TAC)
