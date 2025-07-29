## `type_ssfrag`

``` hol4
simpLib.type_ssfrag : string -> ssfrag
```

------------------------------------------------------------------------

Returns a simpset fragment for simplifying types' constructors.

A call to `type_ssfrag(s)` function returns a simpset fragment that
embodies simplification routines for the type named by the string `s`.
The fragment includes rewrites that express injectivity and disjointness
of constructors, and which simplify `case` expressions applied to terms
that have constructors at the outermost level.

### Failure

Fails if the string argument does not correspond to a type stored in the
`TypeBase`.

### Example

``` hol4
- val ss = simpLib.type_ssfrag "list";
> val ss =
    simpLib.SSFRAG{ac = [], congs = [], convs = [], dprocs = [],
                   filter = NONE,
                   rewrs =
                     [|- (!v f. case v f [] = v) /\
                         !v f a0 a1. case v f (a0::a1) = f a0 a1,
                      |- !a1 a0. ~([] = a0::a1),
                      |- !a1 a0. ~(a0::a1 = []),
                      |- !a0 a1 a0' a1'. (a0::a1 = a0'::a1') =
                                         (a0 = a0') /\ (a1 = a1')]}
     : ssfrag

- SIMP_CONV (bool_ss ++ ss) [] ``h::t = []``;
<<HOL message: inventing new type variable names: 'a>>
> val it = |- (h::t = []) = F : thm
```

### Comments

`RW_TAC` and `SRW_TAC` automatically include these simpset fragments.

### See also

[`BasicProvers.RW_TAC`](#BasicProvers.RW_TAC),
[`BasicProvers.srw_ss`](#BasicProvers.srw_ss),
[`bossLib.type_rws`](#bossLib.type_rws),
[`simpLib.SIMP_CONV`](#simpLib.SIMP_CONV), [`TypeBase`](#TypeBase)
