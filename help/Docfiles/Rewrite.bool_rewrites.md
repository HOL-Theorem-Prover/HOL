## `bool_rewrites` {#Rewrite.bool_rewrites}


```
bool_rewrites: rewrites
```



Contains a number of basic equalities useful in rewriting.


The variable `bool_rewrites` is a basic collection of rewrite rules
useful in expression simplification. The current collection is
    
       - bool_rewrites;
    
       > val it =
           |- (x = x) = T;  |- (T = t) = t;  |- (t = T) = t;  |- (F = t) = ~t;
           |- (t = F) = ~t;  |- ~~t = t;  |- ~T = F;  |- ~F = T;  |- T /\ t = t;
           |- t /\ T = t;  |- F /\ t = F;  |- t /\ F = F;  |- t /\ t = t;
           |- T \/ t = T;  |- t \/ T = T;  |- F \/ t = t;  |- t \/ F = t;
           |- t \/ t = t;  |- T ==> t = t;  |- t ==> T = T;  |- F ==> t = T;
           |- t ==> t = T;  |- t ==> F = ~t;  |- (if T then t1 else t2) = t1;
           |- (if F then t1 else t2) = t2;  |- (!x. t) = t;  |- (?x. t) = t;
           |- (\x. t1) t2 = t1
           Number of rewrite rules = 28
            : rewrites
    




The contents of `bool_rewrites` provide a standard basis upon which to
build bespoke rewrite rule sets for use by the functions in `Rewrite`.

### See also

[`Rewrite.GEN_REWRITE_CONV`](#Rewrite.GEN_REWRITE_CONV), [`Rewrite.GEN_REWRITE_RULE`](#Rewrite.GEN_REWRITE_RULE), [`Rewrite.GEN_REWRITE_TAC`](#Rewrite.GEN_REWRITE_TAC), [`Rewrite.REWRITE_RULE`](#Rewrite.REWRITE_RULE), [`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC), [`Rewrite.add_rewrites`](#Rewrite.add_rewrites), [`Rewrite.add_implicit_rewrites`](#Rewrite.add_implicit_rewrites), [`Rewrite.empty_rewrites`](#Rewrite.empty_rewrites), [`Rewrite.implicit_rewrites`](#Rewrite.implicit_rewrites), [`Rewrite.set_implicit_rewrites`](#Rewrite.set_implicit_rewrites)

