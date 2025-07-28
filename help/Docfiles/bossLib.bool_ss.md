## `bool_ss` {#bossLib.bool_ss}


```
bool_ss : simpset
```



Basic simpset containing standard propositional and first order logic
simplifications, plus beta conversion.


The `bool_ss` simpset is almost at the base of the system-provided
simpset hierarchy.  Though not very powerful, it does include the
following ad hoc collection of rewrite rules for propositions and
first order terms:
    
       |- !A B. ~(A ==> B) = A /\ ~B
       |- !A B. (~(A /\ B) = ~A \/ ~B) /\
                (~(A \/ B) = ~A /\ ~B)
       |- !P. ~(!x. P x) = ?x. ~P x
       |- !P. ~(?x. P x) = !x. ~P x
       |- (~p = ~q) = (p = q)
       |- !x. (x = x) = T
       |- !t. ((T = t) = t) /\
              ((t = T) = t) /\
              ((F = t) = ~t) /\
              ((t = F) = ~t)
       |- (!t. ~~t = t) /\ (~T = F) /\ (~F = T)
       |- !t. (T /\ t = t) /\
              (t /\ T = t) /\
              (F /\ t = F) /\
              (t /\ F = F) /\
              (t /\ t = t)
       |- !t. (T \/ t = T) /\
              (t \/ T = T) /\
              (F \/ t = t) /\
              (t \/ F = t) /\
              (t \/ t = t)
       |- !t. (T ==> t = t) /\
              (t ==> T = T) /\
              (F ==> t = T) /\
              (t ==> t = T) /\
              (t ==> F = ~t)
       |- !t1 t2. ((if T then t1 else t2) = t1) /\
                  ((if F then t1 else t2) = t2)
       |- !t. (!x. t) = t
       |- !t. (?x. t) = t
       |- !b t. (if b then t else t) = t
       |- !a. ?x. x = a
       |- !a. ?x. a = x
       |- !a. ?!x. x = a,
       |- !a. ?!x. a = x,
       |- (!b e. (if b then T else e) = b \/ e) /\
          (!b t. (if b then t else T) = b ==> t) /\
          (!b e. (if b then F else e) = ~b /\ e) /\
          (!b t. (if b then t else F) = b /\ t)
       |- !t. t \/ ~t
       |- !t. ~t \/ t
       |- !t. ~(t /\ ~t)
       |- !x. (@y. y = x) = x
       |- !x. (@y. x = y) = x
       |- !f v. (!x. (x = v) ==> f x) = f v
       |- !f v. (!x. (v = x) ==> f x) = f v
       |- !P a. (?x. (x = a) /\ P x) = P a
       |- !P a. (?x. (a = x) /\ P x) = P a
    
Also included in `bool_ss` is a conversion to perform beta reduction, as
well as the following congruence rules, which allow the simplifier to glean
additional contextual information as it descends through implications and
conditionals.
    
       |- !x x' y y'.
           (x = x') ==>
           (x' ==> (y = y')) ==> (x ==> y = x' ==> y')
    
       |- !P Q x x' y y'.
           (P = Q) ==>
           (Q ==> (x = x')) ==>
           (~Q ==> (y = y')) ==> ((if P then x else y) = (if Q then x' else y'))
    

### Failure

Can’t fail, as it is not a functional value.


The `bool_ss` simpset is an appropriate simpset from which to build
new user-defined simpsets. It is also useful in its own right, for
example when a delicate simplification is desired, where other more
powerful simpsets might cause undue disruption to a goal.  If even
less system rewriting is desired, the `pure_ss` value can be used.

### See also

[`pureSimps.pure_ss`](#pureSimps.pure_ss), [`bossLib.std_ss`](#bossLib.std_ss), [`bossLib.arith_ss`](#bossLib.arith_ss), [`bossLib.list_ss`](#bossLib.list_ss), [`bossLib.SIMP_CONV`](#bossLib.SIMP_CONV), [`bossLib.SIMP_TAC`](#bossLib.SIMP_TAC), [`bossLib.RW_TAC`](#bossLib.RW_TAC)

