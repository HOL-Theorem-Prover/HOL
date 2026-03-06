## `IPSPECL`

``` hol4
PairRules.IPSPECL : (term list -> thm -> thm)
```

------------------------------------------------------------------------

Specializes a theorem zero or more times, with type instantiation if
necessary.

`IPSPECL` is an iterative version of `IPSPEC`

``` hol4
         A |- !p1...pn.tm
   ----------------------------  IPSPECL ["q1",...,"qn"]
    A |- t[q1,...qn/p1,...,pn]
```

(where `qi` is free for `pi` in `tm`).

### Failure

`IPSPECL` fails if the list of terms is longer than the number of
quantified variables in the term, if the type instantiation fails, or if
the type variable being instantiated is free in the assumptions.

### See also

[`Drule.ISPECL`](#Drule.ISPECL), [`Thm.INST_TYPE`](#Thm.INST_TYPE),
[`Drule.INST_TY_TERM`](#Drule.INST_TY_TERM),
[`PairRules.IPSPEC`](#PairRules.IPSPEC), [`Thm.SPEC`](#Thm.SPEC),
[`PairRules.PSPECL`](#PairRules.PSPECL)
