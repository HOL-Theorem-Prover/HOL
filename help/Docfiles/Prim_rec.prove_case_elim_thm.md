## `prove_case_elim_thm`

``` hol4
Prim_rec.prove_case_elim_thm : {case_def : thm, nchotomy : thm} -> thm
```

------------------------------------------------------------------------

Proves a theorem that eliminates applications of case constants with
boolean type.

If `case_def` is the definition of a data type's case constant, where
each clause is of the form

``` hol4
   !a1 .. ai f1 .. fm. type_CASE (ctor_i a1 .. ai) f1 .. fm = f_i a1 .. ai
```

and if `nchotomy` is a theorem describing how a data type's values are
classified by constructor, of the form

``` hol4
   !v. (?a1 .. ai. v = ctor_1 a1 .. ai) \/
       (?b1 .. bj. v = ctor_2 b1 .. bj) \/
       ...
```

then a call to
`prove_case_elim_thm{case_def = case_def, nchotomy = nchotomy}` will
return a theorem of the form

``` hol4
   type_CASE v f1 .. fm <=>
     (?a1 .. ai. v = ctor_1 a1 .. ai /\ f1 a1 .. ai) \/
     (?b1 .. bj. v = ctor_2 b1 .. bj /\ f2 b1 .. bj) \/
     ...
```

Used as a rewrite theorem, this result will "eliminate" occurrences of
the case-constant from a term, when the case-constant term has boolean
type.

### Failure

Will fail if the provided theorems are not of the required form. The
theorems stored in the `TypeBase` are of the correct form. The theorem
returned by `Prim_rec.prove_cases_thm` is of the correct form for the
`nchotomy` argument to this function.

### Example

``` hol4
> prove_case_elim_thm {case_def = TypeBase.case_def_of ``:num``,
                       nchotomy = TypeBase.nchotomy_of ``:num``};
val it = |- num_CASE x v f <=> (x = 0) /\ v \/ ?n. (x = SUC n) /\ f n : thm

> prove_case_elim_thm {case_def = TypeBase.case_def_of ``:bool``,
                       nchotomy = TypeBase.nchotomy_of ``:bool``};
val it =
  |- (if x then t1 else t2) <=> (x <=> T) /\ t1 \/ (x <=> F) /\ t2 : thm
```

### See also

[`Prim_rec.prove_cases_thm`](#Prim_rec.prove_cases_thm),
[`Prim_rec.prove_case_rand_thm`](#Prim_rec.prove_case_rand_thm)
