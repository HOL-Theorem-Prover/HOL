## `ISPEC`

``` hol4
Drule.ISPEC : (term -> thm -> thm)
```

------------------------------------------------------------------------

Specializes a theorem, with type instantiation if necessary.

This rule specializes a quantified variable as does `SPEC`; it differs
from it in also instantiating the type if needed:

``` hol4
     A |- !x:ty.tm
  -----------------------  ISPEC "t:ty'"
      A |- tm[t/x]
```

(where `t` is free for `x` in `tm`, and `ty'` is an instance of `ty`).

### Failure

`ISPEC` fails if the input theorem is not universally quantified, if the
type of the given term is not an instance of the type of the quantified
variable, or if the type variable is free in the assumptions.

### See also

[`Drule.INST_TY_TERM`](#Drule.INST_TY_TERM),
[`Thm.INST_TYPE`](#Thm.INST_TYPE), [`Drule.ISPECL`](#Drule.ISPECL),
[`Thm.SPEC`](#Thm.SPEC), [`Term.match_term`](#Term.match_term)
