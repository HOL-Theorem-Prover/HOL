## `IMP_CONV`

``` hol4
reduceLib.IMP_CONV : conv
```

------------------------------------------------------------------------

Simplifies certain implicational expressions.

If `tm` corresponds to one of the forms given below, where `t` is an
arbitrary term of type `bool`, then `IMP_CONV tm` returns the
corresponding theorem. Note that in the last case the antecedent and
consequent need only be alpha-equivalent rather than strictly identical.

``` hol4
   IMP_CONV “T ==> t” = |- T ==> t = t
   IMP_CONV “t ==> T” = |- t ==> T = T
   IMP_CONV “F ==> t” = |- F ==> t = T
   IMP_CONV “t ==> F” = |- t ==> F = ~t
   IMP_CONV “t ==> t” = |- t ==> t = T
```

### Failure

`IMP_CONV tm` fails unless `tm` has one of the forms indicated above.

### Example

``` hol4
> IMP_CONV “T ==> F”;
val it =  ⊢ T ⇒ F ⇔ F : thm

> IMP_CONV “F ==> x”;
val it = ⊢ F ⇒ x ⇔ T : thm

> IMP_CONV “(!z:(num)list. z = z) ==> (!x:(num)list. x = x)”;
val it =  ⊢ (∀z. z = z) ⇒ (∀z. z = z) ⇔ T : thm
```
