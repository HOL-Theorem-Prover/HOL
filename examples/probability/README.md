---
author: Chun Tian
---

# Fubini's Theorems under certain definitions of extreal arithmetics #

The formalization of Fubini's theorem [1, p.142]
(`martingaleTheory.FUBINI`) has the following extra antecedents beyond
its statements in textbooks:

```
       (!y. y IN Y ==> pos_fn_integral (X,A,u) (\x. (abs o f) (x,y)) <> PosInf) /\
       (!x. x IN X ==> pos_fn_integral (Y,B,v) (\y. (abs o f) (x,y)) <> PosInf) /\
```

On the other hand, in HOL4's `extrealTheory`, the (unique) value of
`PosInf + NegInf`, `PosInf - PosInf` and `NegInf - NegInf` are
unspecified. It turns out that, by specifying a fixed value (for
`PosInf + NegInf`, etc.), the original Fubini's theorem can be proved
without the above extra antecedents.

[1] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
    Cambridge University Press (2017).
