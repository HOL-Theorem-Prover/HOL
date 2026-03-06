## `IMP_CANON`

``` hol4
Drule.IMP_CANON : (thm -> thm list)
```

------------------------------------------------------------------------

Puts theorem into a 'canonical' form.

`IMP_CANON` puts a theorem in 'canonical' form by removing quantifiers
and breaking apart conjunctions, as well as disjunctions which form the
antecedent of implications. It applies the following transformation
rules:

``` hol4
      A |- t1 /\ t2           A |- !x. t           A |- (t1 /\ t2) ==> t
   -------------------       ------------         ------------------------
    A |- t1   A |- t2           A |- t             A |- t1 ==> (t2 ==> t)

        A |- (t1 \/ t2) ==> t              A |- (?x. t1) ==> t2
   -------------------------------        ----------------------
    A |- t1 ==> t   A |- t2 ==> t          A |- t1[x'/x] ==> t2
```

### Failure

Never fails, but if there is no scope for one of the above reductions,
merely gives a list whose only member is the original theorem.

### Comments

This is a rather ad-hoc inference rule, and its use is not recommended.

### See also

[`Thm.CONJUNCT1`](#Thm.CONJUNCT1), [`Thm.CONJUNCT2`](#Thm.CONJUNCT2),
[`Drule.CONJUNCTS`](#Drule.CONJUNCTS), [`Thm.DISJ1`](#Thm.DISJ1),
[`Thm.DISJ2`](#Thm.DISJ2), [`Thm.EXISTS`](#Thm.EXISTS),
[`Thm.SPEC`](#Thm.SPEC)
