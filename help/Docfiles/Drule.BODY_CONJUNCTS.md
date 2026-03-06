## `BODY_CONJUNCTS`

``` hol4
Drule.BODY_CONJUNCTS : (thm -> thm list)
```

------------------------------------------------------------------------

Splits up conjuncts recursively, stripping away universal quantifiers.

When applied to a theorem, `BODY_CONJUNCTS` recursively strips off
universal quantifiers by specialization, and breaks conjunctions into a
list of conjuncts.

``` hol4
    A |- !x1...xn. t1 /\ (!y1...ym. t2 /\ t3) /\ ...
   --------------------------------------------------  BODY_CONJUNCTS
          [A |- t1, A |- t2, A |- t3, ...]
```

### Failure

Never fails, but has no effect if there are no top-level universal
quantifiers or conjuncts.

### Example

The following illustrates how a typical term will be split:

``` hol4
   - local val tm = Parser.term_parser
                        `!x:bool. A /\ (B \/ (C /\ D)) /\ ((!y:bool. E) /\ F)`
     in
     val x = ASSUME tm
     end;

     val x = . |- !x. A /\ (B \/ C /\ D) /\ (!y. E) /\ F : thm

   - BODY_CONJUNCTS x;
   val it = [. |- A, . |- B \/ C /\ D, . |- E, . |- F] : thm list
```

### See also

[`Thm.CONJ`](#Thm.CONJ), [`Thm.CONJUNCT1`](#Thm.CONJUNCT1),
[`Thm.CONJUNCT2`](#Thm.CONJUNCT2),
[`Drule.CONJUNCTS`](#Drule.CONJUNCTS),
[`Tactic.CONJ_TAC`](#Tactic.CONJ_TAC)
