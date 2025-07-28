## `std_ss` {#bossLib.std_ss}


```
std_ss : simpset
```



Basic simplification set.


The simplification set `std_ss` extends `bool_ss` with a useful set
of rewrite rules for terms involving options, pairs, and sums. It
also performs beta and eta reduction. It applies some standard rewrites
to evaluate expressions involving only numerals.

The following rewrites from `pairTheory` are included in `std_ss`:
    
       |- !x. (FST x,SND x) = x
       |- !x y. FST (x,y) = x
       |- !x y. SND (x,y) = y
       |- !x y a b. ((x,y) = (a,b)) = (x = a) /\ (y = b)
       |- !f. CURRY (UNCURRY f) = f
       |- !f. UNCURRY (CURRY f) = f
       |- (CURRY f = CURRY g) = (f = g)
       |- (UNCURRY f = UNCURRY g) = (f = g)
       |- !f x y. CURRY f x y = f (x,y)
       |- !f x y. UNCURRY f (x,y) = f x y
       |- !f g x y. (f ## g) (x,y) = (f x,g y)
    
The following rewrites from `sumTheory` are included in `std_ss`:
    
       |- !x. ISL x ==> (INL (OUTL x) = x)
       |- !x. ISR x ==> (INR (OUTR x) = x)
       |- (!x. ISL (INL x)) /\ !y. ~ISL (INR y)
       |- (!x. ISR (INR x)) /\ !y. ~ISR (INL y)
       |- !x. OUTL (INL x) = x
       |- !x. OUTR (INR x) = x
       |- !x y. ~(INL x = INR y)
       |- !x y. ~(INR y = INL x)
       |- (!y x. (INL x = INL y) = (x = y)) /\
          (!y x. (INR x = INR y) = (x = y))
       |- (!f g x. case f g (INL x) = f x) /\
          (!f g y. case f g (INR y) = g y)
    
The following rewrites from `optionTheory` are included in `std_ss`:
    
       |- (!x y. (SOME x = SOME y) = (x = y))
       |- (!x. ~(NONE = SOME x))
       |- (!x. ~(SOME x = NONE))
       |- (!x. THE (SOME x) = x)
       |- (!x. IS_SOME (SOME x) = T)
       |- (IS_SOME NONE = F)
       |- (!x. IS_NONE x = (x = NONE))
       |- (!x. ~IS_SOME x = (x = NONE))
       |- (!x. IS_SOME x ==> (SOME (THE x) = x))
       |- (!x. case NONE SOME x = x)
       |- (!x. case x SOME x = x)
       |- (!x. IS_NONE x ==> (case e f x = e))
       |- (!x. IS_SOME x ==> (case e f x = f (THE x)))
       |- (!x. IS_SOME x ==> (case e SOME x = x))
       |- (!u f. case u f NONE = u)
       |- (!u f x. case u f (SOME x) = f x)
       |- (!f x. OPTION_MAP f (SOME x) = SOME (f x))
       |- (!f. OPTION_MAP f NONE = NONE)
       |- (OPTION_JOIN NONE = NONE)
       |- (!x. OPTION_JOIN (SOME x) = x)
       |- !f x y. (OPTION_MAP f x = SOME y) = ?z. (x = SOME z) /\ (y = f z)
       |- !f x. (OPTION_MAP f x = NONE) = (x = NONE)
    


For performing obvious simplification steps on terms, formulas, and
goals. Also, sometimes simplification with more powerful simpsets,
like `arith_ss`, becomes too slow, in which case one can use `std_ss`
supplemented with whatever theorems are needed.

### Comments

The simplification sets provided in `BasicProvers` and `bossLib`
(currently `bool_ss`, `std_ss`, `arith_ss`, and `list_ss`) do not
include useful rewrites stemming from HOL datatype declarations, such
as injectivity and distinctness of constructors. However, the
simplification routines `RW_TAC` and `SRW_TAC` automatically load these
rewrites.

### See also

[`BasicProvers.RW_TAC`](#BasicProvers.RW_TAC), [`BasicProvers.SRW_TAC`](#BasicProvers.SRW_TAC), [`simpLib.SIMP_TAC`](#simpLib.SIMP_TAC), [`simpLib.SIMP_CONV`](#simpLib.SIMP_CONV), [`simpLib.SIMP_RULE`](#simpLib.SIMP_RULE), [`BasicProvers.bool_ss`](#BasicProvers.bool_ss), [`bossLib.arith_ss`](#bossLib.arith_ss), [`bossLib.list_ss`](#bossLib.list_ss)

