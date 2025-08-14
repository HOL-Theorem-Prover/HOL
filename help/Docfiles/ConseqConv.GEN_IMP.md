## `GEN_IMP`

``` hol4
ConseqConv.GEN_IMP : term -> thm -> thm
```

------------------------------------------------------------------------

Generalizes both sides of an implication in the conclusion of a theorem.

When applied to a term `x` and a theorem `A |- t1 ==> t2`, the inference
rule `GEN_IMP` returns the theorem `A |- (!x. t1) ==> (!x. t2)`,
provided `x` is a variable not free in any of the assumptions. There is
no compulsion that `x` should be free in `t1` or `t2`.

``` hol4
          A |- (t1 ==> t2)
   ----------------------------     GEN_IMP x       [where x is not free in A]
    A |- (!x. t1) ==> (!x. t2)
```

### Failure

Fails if `x` is not a variable, the conclusion of the theorem is not an
implication, or if `x` is free in any of the assumptions.

### Example

``` hol4
   - val thm0 = mk_thm ([], Term `P (x:'a) ==> Q x`);
   > val thm0 =  |- P (x :'a) ==> Q x : thm

   - val thm1 = GEN_IMP (Term `x:'a`) thm0;
   > val thm1 =  |- (!x. P x) ==> (!x. Q x)
```

### See also

[`Thm.GEN`](#Thm.GEN), [`ConseqConv.GEN_EQ`](#ConseqConv.GEN_EQ)
