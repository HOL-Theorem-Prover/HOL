## `norm_subst`

``` hol4
Term.norm_subst : ((term, term) subst * term set) *
     ((hol_type, hol_type) subst * hol_type list) ->
   (term, term) subst * (hol_type, hol_type) subst
```

------------------------------------------------------------------------

Instantiate term substitution by a type substitution.

Given a term substitution and a type substitution, `norm_subst` applies
the type substitution to the redexes of the term substitution.

The substitutions coming from `raw_match` need to be normalized before
they can be applied by inference rules like `INST_TY_TERM`. An
invocation `raw_match avoid_tys avoid_tms pat ob A` returns a pair of
substitutions `((S,Ids),(T,Idt))`. The `Id` components can be ignored.
The `S` component is a substitution for term variables, but it has to be
instantiated by the type substitution `T` in order to be suitable for
use by `INST_TY_TERM`. In this case, one uses
`norm_subst ((S,Ids),(T,Idt))` as the first argument for `INST_TY_TERM`.

`norm_subst ((S,Ids),(T,Idt))` ignores `Ids` and `Idt`, and returns `T`
unchanged. Where a type-substituted term redex becomes equal to the
corresponding residue, that term redex-residue pair is omitted from the
term substitution returned.

### Failure

Never fails.

### Example

``` hol4
- val ((S,Ids),(T,Idt)) = raw_match [] empty_varset
                    (Term `\x:'a. x = f (y:'b)`)
                    (Term `\a.    a = ~p`) ([],[]);
> val S = [{redex = `(f :'b -> 'a)`, residue = `$~`},
           {redex = `(y :'b)`,       residue = `(p :bool)`}]
    : (term, term) subst

  val T = [{redex = `:'b`, residue = `:bool`},
           {redex = `:'a`, residue = `:bool`}]
        : (hol_type, hol_type) subst

- val (S',_) = norm_subst ((S,Ids),(T,Idt)) ;
> val S' = [{redex = `(y :bool)`,          residue = `(p :bool)`},
        {redex = `(f :bool -> bool)`, residue = `$~`}]
      : (term, term) subst
```

### Comments

Higher level matching routines, like `match_term` and `match_terml`
already return normalized substitutions.

### See also

[`Term.raw_match`](#Term.raw_match),
[`Term.match_term`](#Term.match_term),
[`Term.match_terml`](#Term.match_terml),
[`Drule.INST_TY_TERM`](#Drule.INST_TY_TERM)
