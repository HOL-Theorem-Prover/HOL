## `GEN` {#Thm.GEN}


```
GEN : term -> thm -> thm
```



Generalizes the conclusion of a theorem.


When applied to a term `x` and a theorem `A |- t`, the inference rule
`GEN` returns the theorem `A |- !x. t`, provided `x` is a variable not
free in any of the assumptions. There is no compulsion that `x` should
be free in `t`.
    
          A |- t
       ------------  GEN x                [where x is not free in A]
        A |- !x. t
    



### Failure

Fails if `x` is not a variable, or if it is free in any of the assumptions.

### Example

The following example shows how the above side-condition prevents
the derivation of the theorem `x=T |- !x. x=T`, which is clearly invalid.
    
       - show_types := true;
       > val it = () : unit
    
       - val t = ASSUME (Term `x=T`);
       > val t =  [.] |- (x :bool) = T : thm
    
       - try (GEN (Term `x:bool`)) t;
       Exception raised at Thm.GEN:
       variable occurs free in hypotheses
       ! Uncaught exception:
       ! HOL_ERR
    



### See also

[`Thm.GENL`](#Thm.GENL), [`Drule.GEN_ALL`](#Drule.GEN_ALL), [`Tactic.GEN_TAC`](#Tactic.GEN_TAC), [`Thm.SPEC`](#Thm.SPEC), [`Drule.SPECL`](#Drule.SPECL), [`Drule.SPEC_ALL`](#Drule.SPEC_ALL), [`Tactic.SPEC_TAC`](#Tactic.SPEC_TAC), [`ConseqConv.GEN_ASSUM`](#ConseqConv.GEN_ASSUM), [`ConseqConv.GEN_IMP`](#ConseqConv.GEN_IMP), [`ConseqConv.GEN_EQ`](#ConseqConv.GEN_EQ)

