## `prove_case_eq_thm` {#Prim_rec.prove_case_eq_thm}


```
prove_case_eq_thm : {case_def : thm, nchotomy : thm} -> thm
```



Proves a rewrite for eliminating certain forms of case expression.


If `case_def` is the definition of a data type’s case constant, where
each clause is of the form
    
       !a1 .. ai f1 .. fm. type_CASE (ctor_i a1 .. ai) f1 .. fm = f_i a1 .. ai
    
and if `nchotomy` is a theorem describing how a data type’s values are
classified by constructor, of the form
    
       !v. (?a1 .. ai. v = ctor_1 a1 .. ai) \/
           (?b1 .. bj. v = ctor_2 b1 .. bj) \/
           ...
    
then a call to `prove_case_elim_thm{case_def = case_def, nchotomy = nchotomy}`
will return a theorem of the form
    
       (type_CASE u f1 .. fm = v) <=>
         (?a1 .. ai. u = ctor_1 a1 .. ai /\ f1 a1 .. ai = v) \/
         (?b1 .. bj. u = ctor_2 b1 .. bj /\ f2 b1 .. bj = v) \/
         ...
    

### Failure

Will fail if the provided theorems are not of the required form. The
theorems stored in the `TypeBase` are of the correct form. The theorem
returned by `Prim_rec.prove_cases_thm` is of the correct form for the
`nchotomy` argument to this function.

### See also

[`Prim_rec.prove_case_elim_thm`](#Prim_rec.prove_case_elim_thm), [`Prim_rec.prove_case_rand_thm`](#Prim_rec.prove_case_rand_thm)

