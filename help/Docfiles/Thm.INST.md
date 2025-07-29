## `INST`

``` hol4
Thm.INST : (term,term) subst -> thm -> thm
```

------------------------------------------------------------------------

Instantiates free variables in a theorem.

`INST` is a rule for substituting arbitrary terms for free variables in
a theorem.

``` hol4
             A |- t               INST [x1 |-> t1,...,xn |-> tn]
   -----------------------------
    A[t1,...,tn/x1,...,xn]
     |-
    t[t1,...,tn/x1,...,xn]
```

### Failure

Fails if, for `1 <= i <= n`, some `xi` is not a variable, or if some
`xi` has a different type than its intended replacement `ti`.

### Example

In the following example a theorem is instantiated for a specific term:

``` hol4
   - load"arithmeticTheory";

   - CONJUNCT1 arithmeticTheory.ADD_CLAUSES;
   > val it = |- 0 + m = m : thm

   - INST [``m:num`` |-> ``2*x``]
          (CONJUNCT1 arithmeticTheory.ADD_CLAUSES);

   val it = |- 0 + (2 * x) = 2 * x : thm
```

### See also

[`Drule.INST_TY_TERM`](#Drule.INST_TY_TERM),
[`Thm.INST_TYPE`](#Thm.INST_TYPE), [`Drule.ISPEC`](#Drule.ISPEC),
[`Drule.ISPECL`](#Drule.ISPECL), [`Thm.SPEC`](#Thm.SPEC),
[`Drule.SPECL`](#Drule.SPECL), [`Drule.SUBS`](#Drule.SUBS),
[`Term.subst`](#Term.subst), [`Thm.SUBST`](#Thm.SUBST),
[`Lib.|->`](#Lib..GZKQ4)
