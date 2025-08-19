## `SPEC`

``` hol4
Thm.SPEC : term -> thm -> thm
```

------------------------------------------------------------------------

Specializes the conclusion of a theorem.

When applied to a term `u` and a theorem `A |- !x. t`, then `SPEC`
returns the theorem `A |- t[u/x]`. If necessary, variables will be
renamed prior to the specialization to ensure that `u` is free for `x`
in `t`, that is, no variables free in `u` become bound after
substitution.

``` hol4
     A |- !x. t
   --------------  SPEC u
    A |- t[u/x]
```

### Failure

Fails if the theorem's conclusion is not universally quantified, or if
`x` and `u` have different types.

### Example

The following example shows how `SPEC` renames bound variables if
necessary, prior to substitution: a straightforward substitution would
result in the clearly invalid theorem `|- ~y ==> (!y. y ==> ~y)`.

``` hol4
   - let val xv = Term `x:bool`
         and yv = Term `y:bool`
     in
       (GEN xv o DISCH xv o GEN yv o DISCH yv) (ASSUME xv)
     end;
   > val it = |- !x. x ==> !y. y ==> x : thm

   - SPEC (Term `~y`) it;
   > val it = |- ~y ==> !y'. y' ==> ~y : thm
```

### See also

[`Drule.ISPEC`](#Drule.ISPEC), [`Drule.SPECL`](#Drule.SPECL),
[`Drule.SPEC_ALL`](#Drule.SPEC_ALL),
[`Drule.SPEC_VAR`](#Drule.SPEC_VAR), [`Thm.GEN`](#Thm.GEN),
[`Thm.GENL`](#Thm.GENL), [`Drule.GEN_ALL`](#Drule.GEN_ALL)
