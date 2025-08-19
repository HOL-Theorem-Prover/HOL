## `INST_TYPE`

``` hol4
Thm.INST_TYPE : (hol_type,hol_type) subst -> thm -> thm
```

------------------------------------------------------------------------

Instantiates types in a theorem.

`INST_TYPE` is a primitive rule in the HOL logic, which allows
instantiation of type variables.

``` hol4
              A |- t
  ----------------------------------- INST_TYPE[vty1|->ty1,..., vtyn|->tyn]
   A[ty1,...,tyn/vty1,...,vtyn]
    |-
   t[ty1,...,tyn/vty1,...,vtyn]
```

Type substitution is performed throughout the hypotheses and the
conclusion. Variables will be renamed if necessary to prevent distinct
bound variables becoming identical after the instantiation.

### Failure

Never fails.

`INST_TYPE` enables polymorphic theorems to be used at any type.

### Example

Supposing one wanted to specialize the theorem `EQ_SYM_EQ` for
particular values, the first attempt could be to use `SPECL` as follows:

``` hol4
   - SPECL [``a:num``, ``b:num``] EQ_SYM_EQ;
   uncaught exception HOL_ERR
```

The failure occurred because `EQ_SYM_EQ` contains polymorphic types. The
desired specialization can be obtained by using `INST_TYPE`:

``` hol4
   - load "numTheory";

   - SPECL [Term `a:num`, Term`b:num`]
           (INST_TYPE [alpha |-> Type`:num`] EQ_SYM_EQ);

   > val it = |- (a = b) = (b = a) : thm
```

### See also

[`Term.inst`](#Term.inst), [`Thm.INST`](#Thm.INST),
[`Drule.INST_TY_TERM`](#Drule.INST_TY_TERM), [`Lib.|->`](#Lib..GZKQ4)
