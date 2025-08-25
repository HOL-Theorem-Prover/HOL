## `prove_case_rand_thm`

``` hol4
Prim_rec.prove_case_rand_thm : {case_def : thm, nchotomy : thm} -> thm
```

------------------------------------------------------------------------

Proves a theorem that "lifts" applied case constants up within a term.

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
`prove_case_rand_thm{case_def = case_def, nchotomy = nchotomy}` will
return a theorem of the form

``` hol4
   f (type_CASE x f1 .. fm) =
     type_CASE x (\a1 .. ai. f (f1 a1 .. ai))
                 (\b1 .. bj. f (f2 b1 .. bj))
                 ...
```

Given the typical pretty-printing provided for case-terms, the
right-hand side of the above theorem will actually print as

``` hol4
   case x of
      ctor_1 a1 .. ai => f (f1 a1 .. ai)
    | ctor_2 b1 .. bj => f (f2 b1 .. bj)
    | ...
```

### Failure

Will fail if the provided theorems are not of the required form. The
theorems stored in the `TypeBase` are of the correct form. The theorem
returned by `Prim_rec.prove_cases_thm` is of the correct form for the
`nchotomy` argument to this function.

### Example

``` hol4
> prove_case_rand_thm {case_def = TypeBase.case_def_of ``:num``,
                       nchotomy = TypeBase.nchotomy_of ``:num``};
val it =
   |- f' (num_CASE x v f) = case x of 0 => f' v | SUC n => f' (f n):
   thm
```

### See also

[`Prim_rec.prove_cases_thm`](#Prim_rec.prove_cases_thm)
