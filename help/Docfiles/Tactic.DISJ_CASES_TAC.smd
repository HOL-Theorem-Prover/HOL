## `DISJ_CASES_TAC`

``` hol4
Tactic.DISJ_CASES_TAC : thm_tactic
```

------------------------------------------------------------------------

Produces a case split based on a disjunctive theorem.

Given a theorem `th` of the form `A |- u \/ v`, `DISJ_CASES_TAC th`
applied to a goal produces two subgoals, one with `u` as an assumption
and one with `v`:

``` hol4
              A ?- t
   ============================  DISJ_CASES_TAC (A |- u \/ v)
    A u {u} ?- t   A u {v}?- t
```

### Failure

Fails if the given theorem does not have a disjunctive conclusion.

### Example

Given the simple fact about arithmetic `th`,
`|- (m = 0) \/ (?n. m = SUC n)`, the tactic `DISJ_CASES_TAC th` can be
used to produce a case split:

``` hol4
   - DISJ_CASES_TAC th ([],Term`(P:num -> bool) m`);
   ([([`m = 0`], `P m`),
     ([`?n. m = SUC n`], `P m`)], fn) : tactic_result
```

Performing a case analysis according to a disjunctive theorem.

### See also

[`Tactic.ASSUME_TAC`](#Tactic.ASSUME_TAC),
[`Tactic.ASM_CASES_TAC`](#Tactic.ASM_CASES_TAC),
[`Tactic.COND_CASES_TAC`](#Tactic.COND_CASES_TAC),
[`Thm_cont.DISJ_CASES_THEN`](#Thm_cont.DISJ_CASES_THEN),
[`Tactic.STRUCT_CASES_TAC`](#Tactic.STRUCT_CASES_TAC)
