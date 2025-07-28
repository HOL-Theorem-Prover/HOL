## `match_terml` {#Term.match_terml}


```
match_terml
     : hol_type list -> term set -> term -> term
       -> (term,term) subst * (hol_type,hol_type) subst
```



Match two terms while restricting some instantiations.


An invocation `match_terml avoid_tys avoid_tms pat ob (tmS,tyS)`, if
it does not raise an exception, returns a pair of substitutions `(S,T)`
such that
    
       aconv (subst S (inst T pat)) ob.
    
The arguments `avoid_tys` and `avoid_tms` specify type
and term variables in `pat` that are not allowed to become `redex`es
in `S` and `T`.

### Failure

`match_terml` will fail if no `S` and `T` meeting the above requirements
can be found. If a match `(S,T)` between `pat` and `ob` can be found,
but elements of `avoid_tys` would appear as redexes in `T` or
elements of `avoid_tms` would appear as redexes in `S`, then
`match_terml` will also fail.

### Example

    
    - val (S,T) = match_terml [] empty_varset
                      (Term `\x:'a. x = f (y:'b)`)
                      (Term `\a.    a = ~p`);
    > val S = [{redex = `(f :'b -> 'a)`, residue = `$~`},
               {redex = `(y :'b)`,       residue = `(p :bool)`}] : ...
    
      val T = [{redex = `:'b`, residue = `:bool`},
               {redex = `:'a`, residue = `:bool`}] : ...
    
    - match_terml [alpha] empty_varset  (* forbid instantiation of 'a *)
              (Term `\x:'a. x = f (y:'b)`)
              (Term `\a.    a = ~p`);
    ! Uncaught exception:
    ! HOL_ERR
    
    - match_terml [] (HOLset.add(empty_varset,mk_var("y",beta)))
              (Term `\x:'a. x = f (y:'b)`)
              (Term `\a.    a = ~p`);
    ! Uncaught exception:
    ! HOL_ERR
    



### See also

[`Term.match_term`](#Term.match_term), [`Term.raw_match`](#Term.raw_match), [`Term.subst`](#Term.subst), [`Term.inst`](#Term.inst), [`Type.match_typel`](#Type.match_typel), [`Type.type_subst`](#Type.type_subst)

