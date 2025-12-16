## `IPSPEC`

``` hol4
PairRules.IPSPEC : (term -> thm -> thm)
```

------------------------------------------------------------------------

Specializes a theorem, with type instantiation if necessary.

This rule specializes a paired quantification as does `PSPEC`; it
differs from it in also instantiating the type if needed:

``` hol4
     A |- !p:ty.tm
  -----------------------  IPSPEC "q:ty'"
      A |- tm[q/p]
```

(where `q` is free for `p` in `tm`, and `ty'` is an instance of `ty`).

### Failure

`IPSPEC` fails if the input theorem is not universally quantified, if
the type of the given term is not an instance of the type of the
quantified variable, or if the type variable is free in the assumptions.

### See also

[`Drule.ISPEC`](#Drule.ISPEC),
[`Drule.INST_TY_TERM`](#Drule.INST_TY_TERM),
[`Thm.INST_TYPE`](#Thm.INST_TYPE),
[`PairRules.IPSPECL`](#PairRules.IPSPECL),
[`PairRules.PSPEC`](#PairRules.PSPEC), [`DB.match`](#DB.match)
