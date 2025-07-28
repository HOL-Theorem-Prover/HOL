## `subst` {#Term.subst}


```
subst : (term,term) subst -> term -> term
```



Substitutes terms in a term.


Given a "(term,term) subst" (a list of `{redex, residue}` records) and a
term `tm`, `subst` attempts to replace each free occurrence of a
`redex` in `tm` by its associated `residue`. The substitution is done in
parallel, i.e., once a redex has been replaced by its residue, at some
place in the term, that residue at that place will not itself be
replaced in the current call. When necessary, renaming of bound
variables in `tm` is done to avoid capturing the free variables of an
incoming residue.

### Failure

Failure occurs if there exists a `{redex, residue}` record in the
substitution such that the types of the `redex` and `residue` are not
equal.

### Example

    
    - load "arithmeticTheory";
    
    - subst [Term`SUC 0` |-> Term`1`]
            (Term`SUC(SUC 0)`);
    > val it = `SUC 1` : term
    
    - subst [Term`SUC 0` |-> Term`1`,
             Term`SUC 1` |-> Term`2`]
            (Term`SUC(SUC 0)`);
    > val it = `SUC 1` : term
    
    - subst [Term`SUC 0` |-> Term`1`,
             Term`SUC 1` |-> Term`2`]
            (Term`SUC(SUC 0) = SUC 1`);
    > val it = `SUC 1 = 2` : term
    
    - subst [Term`b:num` |-> Term`a:num`]
            (Term`\a:num. b:num`);
    > val it = `\a'. a` : term
    
    - subst [Term`flip:'a` |-> Term`foo:'a`]
            (Term`waddle:'a`);
    > val it = `waddle` : term
    



### See also

[`Term.inst`](#Term.inst), [`Thm.SUBST`](#Thm.SUBST), [`Drule.SUBS`](#Drule.SUBS), [`Lib.|->`](#Lib..GZKQ4)

