## `SRW_TAC` {#bossLib.SRW_TAC}


```
SRW_TAC : ssfrag list -> thm list -> tactic
```



A version of `RW_TAC` with an implicit `simpset`.


A call to `SRW_TAC [d1,...,dn] thlist` produces the same result as
    
       RW_TAC (srw_ss() ++ d1 ++ ... ++ dn) thlist
    

### Failure

When applied to a goal, the tactic resulting from an application of
`SRW_TAC` may diverge.

### Comments

There are two reasons why one might prefer `SRW_TAC` to `RW_TAC`.
Firstly, when a large number of datatypes are present in the
`TypeBase`, the implementation of `RW_TAC` has to merge the attendant
simplifications for each type onto its `simpset` argument each time it
is called.  This can be rather time-consuming.  Secondly, the
`simpset` returned by `srw_ss()` can be augmented with fragments from
other sources than the `TypeBase`, using the functions `augment_srw_ss`
and `export_rewrites`.  This can make for a tool that is simple to
use, and powerful because of all its accumulated `simpset` fragments.

Naturally, the latter advantage can also be a disadvantage: if
`SRW_TAC` does too much because there is too much in the `simpset`
underneath `srw_ss()`, then there is no way to get around this using
`SRW_TAC`.

Typical invocations of `SRW_TAC` will be of the form
    
       SRW_TAC [][th1, th2,.. ]
    
The first argument, for lists of `simpset` fragments is for the
inclusion of fragments that are not always appropriate.  An example of
such a fragment is `numSimps.ARITH_ss`, which embodies an arithmetic
decision procedure for the natural numbers.

### See also

[`bossLib.srw_ss`](#bossLib.srw_ss), [`bossLib.augment_srw_ss`](#bossLib.augment_srw_ss), [`BasicProvers.export_rewrites`](#BasicProvers.export_rewrites), [`simpLib.SSFRAG`](#simpLib.SSFRAG)

