## `dest_imp` {#boolSyntax.dest_imp}


```
dest_imp : term -> term * term
```



Breaks an implication or negation into antecedent and consequent.


`dest_imp` is a term destructor for implications. It treats negations as
implications with consequent `F`. Thus, if `M` is a term with the form
`t1 ==> t2`, then `dest_imp M` returns `(t1,t2)`, and if `M` has the
form `~t`, then `dest_imp M` returns `(t,F)`.

### Failure

Fails if `M` is neither an implication nor a negation.

### Comments

Destructs negations for increased functionality of HOL-style resolution.
If the ability to destruct negations is not desired, as is only right,
then use `dest_imp_only`.

### See also

[`boolSyntax.mk_imp`](#boolSyntax.mk_imp), [`boolSyntax.dest_imp_only`](#boolSyntax.dest_imp_only), [`boolSyntax.is_imp`](#boolSyntax.is_imp), [`boolSyntax.is_imp_only`](#boolSyntax.is_imp_only), [`boolSyntax.strip_imp`](#boolSyntax.strip_imp), [`boolSyntax.list_mk_imp`](#boolSyntax.list_mk_imp)

