## `raw_match`

``` hol4
Term.raw_match :
  hol_type list -> term set ->
  term -> term ->
  (term,term) subst * (hol_type,hol_type) subst ->
    ((term,term) subst * term set) *
    ((hol_type,hol_type) subst * hol_type list)
```

------------------------------------------------------------------------

Primitive term matcher.

The most primitive matching algorithm for HOL terms is `raw_match`. An
invocation `raw_match avoid_tys avoid_tms pat ob (tmS,tyS)`, if it
succeeds, returns a substitution pair `((TmS,TmID),(TyS,TyID))` such
that

``` hol4
   aconv (subst TmS' (inst TyS pat)) ob.
```

where `TmS'` is `TmS` instantiated by `TyS`. The arguments `avoid_tys`
and `avoid_tms` specify type and term variables in `pat` that are not
allowed to become `redex`es in `S` and `T`.

The pair `(tmS,tyS)` is an accumulator argument. This allows `raw_match`
to be folded through lists of terms to be matched. `(TmS,TyS)` must
agree with `(tmS,tyS)`. This means that if there is a `{redex,residue}`
in `TmS` and also a `{redex,residue}` in `tmS` so that both `redex`
fields are equal, then the `residue` fields must be alpha-convertible.
Similarly for types: if there is a `{redex,residue}` in `TyS` and also a
`{redex,residue}` in `tyS` so that both `redex` fields are equal, then
the `residue` fields must also be equal. If these conditions hold, then
the result-pair `(TmS,TyS)` includes `(tmS,tyS)`.

Finally, note that the result also includes a set (resp. a list) of term
and type variables, accompanying the substitutions. These represent
identity bindings that have occurred in the process of doing the match.
If `raw_match` is to be folded across multiple problems, these output
values will need to be merged with `avoid_tms` and `avoid_tys`
respectively on the next call so that they cannot be instantiated a
second time. Because they are identity bindings, they do not need to be
referred to in validating the central identity above.

### Failure

`raw_match` will fail if no `TmS` and `TyS` meeting the above
requirements can be found. If a match `(TmS,TyS)` between `pat` and `ob`
can be found, but elements of `avoid_tys` would appear as redexes in
`TyS` or elements of `avoid_tms` would appear as redexes in `TmS`, then
`raw_match` will also fail.

### Example

We first perform a match that requires type instantitations, and also
alpha-convertibility.

``` hol4
   > val ((S,_),(T,_)) =
       raw_match [] empty_varset
                 (Term `\x:'a. x = f (y:'b)`)
                 (Term `\a.    a = ~p`) ([],[]);
   val S =
     [{redex = `(y :'b)`,       residue = `(p :bool)`},
      {redex = `(f :'b -> 'a)`, residue = `$~`}] : ...

   val T =
     [{redex = `:'b`, residue = `:bool`},
      {redex = `:'a`, residue = `:bool`}] : ...
```

One of the main differences between `raw_match` and more refined
derivatives of it, is that the returned substitutions are un-normalized
by `raw_match`. If one naively applied `(S,T)` to `\x:'a. x = f (y:'b)`,
type instantiation with `T` would be applied first, yielding
`\x:bool. x = f (y:bool)`. Then substitution with `S` would be applied,
unsuccessfully, since both `f` and `y` in the pattern term have been
type instantiated, but the corresponding elements of the substitution
haven't. Thus, higher level operations building on `raw_match` typically
instantiate `S` by `T` to get `S'` before applying `(S',T)` to the
pattern term. This can be achieved by using `norm_subst`. However,
`raw_match` exposes this level of detail to the programmer.

### Comments

Higher level matchers are generally preferable, but `raw_match` is
occasionally useful when programming inference rules.

### See also

[`Term.match_term`](#Term.match_term),
[`Term.match_terml`](#Term.match_terml),
[`Term.norm_subst`](#Term.norm_subst), [`Term.subst`](#Term.subst),
[`Term.inst`](#Term.inst),
[`Type.raw_match_type`](#Type.raw_match_type),
[`Type.match_type`](#Type.match_type),
[`Type.match_typel`](#Type.match_typel),
[`Type.type_subst`](#Type.type_subst)
