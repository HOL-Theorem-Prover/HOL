## `INDUCT_THEN` {#Prim_rec.INDUCT_THEN}


```
INDUCT_THEN : (thm -> thm_tactic -> tactic)
```



Structural induction tactic for automatically-defined concrete types.


The function `INDUCT_THEN` implements structural induction tactics for
arbitrary concrete recursive types of the kind definable by `define_type`.  The
first argument to `INDUCT_THEN` is a structural induction theorem for the
concrete type in question. This theorem must have the form of an induction
theorem of the kind returned by `prove_induction_thm`. When applied to such a
theorem, the function `INDUCT_THEN` constructs specialized tactic for
doing structural induction on the concrete type in question.

The second argument to `INDUCT_THEN` is a function that determines what is be
done with the induction hypotheses in the goal-directed proof by structural
induction.  Suppose that `th` is a structural induction theorem for a concrete
data type `ty`, and that `A ?- !x.P` is a universally-quantified goal in which
the variable `x` ranges over values of type `ty`. If the type `ty` has `n`
constructors `C1`, ..., `Cn` and ‘`Ci(vs)`’ represents a (curried) application
of the `i`th constructor to a sequence of variables, then if `ttac` is a
function that maps the induction hypotheses `hypi` of the `i`th subgoal
to the tactic:
    
          A  ?- P[Ci(vs)/x]
       ======================  MAP_EVERY ttac hypi
             A1 ?- Gi
    
then `INDUCT_THEN th ttac` is an induction tactic that decomposes
the goal `A ?- !x.P` into a set of `n` subgoals, one for each constructor,
as follows:
    
                A ?- !x.P
      ================================  INDUCT_THEN th ttac
         A1 ?- G1  ...   An ?- Gn
    
The resulting subgoals correspond to the cases in a structural
induction on the variable `x` of type `ty`, with induction hypotheses treated
as determined by `ttac`.

### Failure

`INDUCT_THEN th ttac g` fails if `th` is not a structural induction theorem of
the form returned by `prove_induction_thm`, or if the goal does not have the
form `A ?- !x:ty.P` where `ty` is the type for which `th` is the induction
theorem, or if `ttac` fails for any subgoal in the induction.

### Example

The built-in structural induction theorem for lists is:
    
       |- !P. P[] /\ (!t. P t ==> (!h. P(CONS h t))) ==> (!l. P l)
    
When `INDUCT_THEN` is applied to this theorem, it constructs
and returns a specialized induction tactic (parameterized by a theorem-tactic)
for doing induction on lists:
    
       - val LIST_INDUCT_THEN = INDUCT_THEN listTheory.list_INDUCT;
    
The resulting function, when supplied with the `thm_tactic`
`ASSUME_TAC`, returns a tactic that decomposes a goal `?- !l.P[l]` into the
base case `?- P[NIL]` and a step case `P[l] ?- !h. P[CONS h l]`, where the
induction hypothesis `P[l]` in the step case has been put on the assumption
list.  That is, the tactic:
    
       LIST_INDUCT_THEN ASSUME_TAC
    
does structural induction on lists, putting any induction hypotheses
that arise onto the assumption list:
    
                          A ?- !l. P
       =======================================================
        A |- P[NIL/l]   A u {P[l'/l]} ?- !h. P[(CONS h l')/l]
    
Likewise `LIST_INDUCT_THEN STRIP_ASSUME_TAC` will also do induction
on lists, but will strip induction hypotheses apart before adding them to the
assumptions (this may be useful if P is a conjunction or a disjunction, or is
existentially quantified).  By contrast, the tactic:
    
       LIST_INDUCT_THEN MP_TAC
    
will decompose the goal as follows:
    
                          A ?- !l. P
       =====================================================
        A |- P[NIL/l]   A ?- P[l'/l] ==> !h. P[CONS h l'/l]
    
That is, the induction hypothesis becomes the antecedent of an
implication expressing the step case in the induction, rather than an
assumption of the step-case subgoal.

### See also

[`Prim_rec.new_recursive_definition`](#Prim_rec.new_recursive_definition), [`Prim_rec.prove_cases_thm`](#Prim_rec.prove_cases_thm), [`Prim_rec.prove_constructors_distinct`](#Prim_rec.prove_constructors_distinct), [`Prim_rec.prove_constructors_one_one`](#Prim_rec.prove_constructors_one_one), [`Prim_rec.prove_induction_thm`](#Prim_rec.prove_induction_thm), [`Prim_rec.prove_rec_fn_exists`](#Prim_rec.prove_rec_fn_exists)

