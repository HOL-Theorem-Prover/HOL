## `ISPECL`

``` hol4
Drule.ISPECL : term list -> thm -> thm
```

------------------------------------------------------------------------

Specializes a theorem zero or more times, with type instantiation if
necessary.

`ISPECL` is an iterative version of `ISPEC`

``` hol4
         A |- !x1...xn.t
   ----------------------------  ISPECL [t1,...,tn]
    A |- t[t1,...tn/x1,...,xn]
```

(where `ti` is free for `xi` in `tm`).

### Failure

`ISPECL` fails if the list of terms is longer than the number of
quantified variables in the term, if the type instantiation fails, or if
the type variable being instantiated is free in the assumptions.

### See also

[`Thm.INST_TYPE`](#Thm.INST_TYPE),
[`Drule.INST_TY_TERM`](#Drule.INST_TY_TERM),
[`Drule.ISPEC`](#Drule.ISPEC), [`Drule.PART_MATCH`](#Drule.PART_MATCH),
[`Thm.SPEC`](#Thm.SPEC), [`Drule.SPECL`](#Drule.SPECL)
