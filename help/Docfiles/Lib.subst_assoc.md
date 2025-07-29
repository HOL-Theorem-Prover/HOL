## `subst_assoc`

``` hol4
Lib.subst_assoc : ('a -> bool) -> ('a,'b)subst -> 'b option
```

------------------------------------------------------------------------

Treats a substitution as an association list.

An application
`subst_assoc P [{redex_1,residue_1},...,{redex_n,residue_n}]` returns
`SOME residue_i` if `P` holds of `redex_i`, and did not hold (or fail)
for `{redex_j | 1 <= j < i}`. If `P` holds for none of the `redex`es in
the substitution, `NONE` is returned.

### Failure

If `P redex_i` fails for some `redex` encountered in the left-to-right
traversal of the substitution.

### Example

``` hol4
- subst_assoc is_abs [T |-> F, Term `\x.x` |-> Term `combin$I`];
> val it = SOME`I` : term option
```

### See also

[`Lib.assoc`](#Lib.assoc), [`Lib.rev_assoc`](#Lib.rev_assoc),
[`Lib.assoc1`](#Lib.assoc1), [`Lib.assoc2`](#Lib.assoc2),
[`Lib.|->`](#Lib..GZKQ4)
