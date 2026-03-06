## `match_term`

``` hol4
Term.match_term : term -> term -> (term,term) subst * (hol_type,hol_type) subst
```

------------------------------------------------------------------------

Finds instantiations to match one term to another.

An application `match_term M N` attempts to find a set of type and term
instantiations for `M` to make it alpha-convertible to `N`. If
`match_term` succeeds, it returns the instantiations in the form of a
pair containing a term substitution and a type substitution. In
particular, if `match_term pat ob` succeeds in returning a value
`(S,T)`, then

``` hol4
   aconv (subst S (inst T pat)) ob.
```

### Failure

Fails if the term cannot be matched by one-way instantiation. If the
pattern includes variables of the same name but different types, the
resulting type instantiation may cause those variables to be identified
and the term instantiation to be useless.

### Example

The following shows how `match_term` could be used to match the
conclusion of a theorem to a term.

``` hol4
   > val th = REFL (Term `x:'a`);
   val th = |- x = x : thm

   > match_term (concl th) (Term `1 = 1`);
   val it = ([{redex = `x`, residue = `1`}],
             [{redex = `:'a`, residue = `:num`}])
     : term subst * hol_type subst

   > INST_TY_TERM it th;
   val it = |- 1 = 1
```

The following shows an attempt to use a bad pattern (the pattern term
`t` has two variables called `x` at different types):

``` hol4
   > val _ = show_types := true;
   > val t = list_mk_comb(``f:'a -> 'b -> 'c``, [``x:'a``, ``x:'b``]);
   val t = ``(f : 'a -> 'b -> 'c) (x:'a) (x:'b)``;

   > val (tminst, tyinst) = match_term t ``(g: 'a -> 'a -> 'b) a b``;
   val tminst =
      [{redex = ``(f :'a -> 'a -> 'b)``,
        residue = ``(g :'a -> 'a -> 'b)``},
       {redex = ``(x :'a)``, residue = ``(a :'a)``},
       {redex = ``(x :'a)``, residue = ``(b :'a)``}]:
      (term, term) Term.subst
   val tyinst =
      [{redex = ``:'c``, residue = ``:'b``},
       {redex = ``:'b``, residue = ``:'a``}]:
      (hol_type, hol_type) Term.subst
```

The `tminst` value is unusable as it seeks to instantiate two different
`x` variables (one with `a`, one with `b`) that are now actually the
same variable.

### Comments

For instantiating theorems `PART_MATCH` is usually easier to use.

### See also

[`Term.match_terml`](#Term.match_terml),
[`Type.match_type`](#Type.match_type),
[`Drule.INST_TY_TERM`](#Drule.INST_TY_TERM),
[`Drule.PART_MATCH`](#Drule.PART_MATCH)
