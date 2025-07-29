## `RESQ_SPECL`

``` hol4
res_quanTools.RESQ_SPECL : (term list -> thm -> thm)
```

------------------------------------------------------------------------

Specializes zero or more variables in the conclusion of a restricted
universally quantified theorem.

When applied to a term list `[u1;...;un]` and a theorem
`A |- !x1::P1. ... !xn::Pn. t`, the inference rule `RESQ_SPECL` returns
the theorem

``` hol4
   A,P1 u1,...,Pn un |- t[u1/x1]...[un/xn]
```

where the substitutions are made sequentially left-to-right in the same
way as for `RESQ_SPEC`, with the same sort of alpha-conversions applied
to `t` if necessary to ensure that no variables which are free in `ui`
become bound after substitution.

``` hol4
           A |- !x1::P1. ... !xn::Pn. t
   --------------------------------------------  RESQ_SPECL "[u1;...;un]"
     A,P1 u1, ..., Pn un |- t[u1/x1]...[un/xn]
```

It is permissible for the term-list to be empty, in which case the
application of `RESQ_SPECL` has no effect.

### Failure

Fails if one of the specialization of the restricted universally
quantified variable in the original theorem fails.

### See also

[`res_quanTools.RESQ_GEN_TAC`](#res_quanTools.RESQ_GEN_TAC),
[`res_quanTools.RESQ_SPEC`](#res_quanTools.RESQ_SPEC)
