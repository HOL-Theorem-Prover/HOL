## `list_mk_icomb`

``` hol4
boolSyntax.list_mk_icomb : term * term list -> term
```

------------------------------------------------------------------------

Folds `mk_icomb` over a series of arguments.

A call to `list_mk_icomb(f,args)` combines `f` with each of the elements
of the list `args` in turn, moving from left to right. If `args` is
empty, then the result is simply `f`. When `args` is non-empty, the
growing application-term is created with successive calls to `mk_icomb`,
possibly causing type variables in any of the terms to become
instantiated.

### Failure

Fails if any of the underlying calls to `mk_icomb` fails, which will
occur if the type of the accumulating term (starting with `f`) is not of
a function type, or if it has a domain type that can not be instantiated
to equal the type of the next argument term.

### Comments

`list_mk_icomb` is to `mk_icomb` what `list_mk_comb` is to
`mk_comb`. However, it is important to be aware that `list_mk_icomb`
instantiates types sequentially, and not, as one might expect, in
parallel. For example the pairing function `(,)` is usually written
infix and has type `:'a -> 'b -> 'a # 'b`. A pair where the first
component has type `:'b` and the second has type `:num` can be
built with
```
> pairSyntax.mk_pair(``x:'b``, ``y:num``);
val it = “(x,y)”: term
> type_of it;
val it = “:β # num”: hol_type
```
but an attempt to do the same via `list_mk_icomb`
```
> list_mk_icomb
    (``(,):'a -> 'b -> 'a # 'b``, [``x:'b``, ``y:num``]);
val it = “(x,y)”: term
> type_of it;
val it = “:num # num”: hol_type
```
confounds expectations since the call first instantiates `:'a` in the
type of `(,)` by `:'b`, then instantiates `:'b` in the result by
`:num`.

### See also

[`Term.list_mk_comb`](#Term.list_mk_comb),
[`Term.mk_comb`](#Term.mk_comb),
[`boolSyntax.mk_icomb`](#boolSyntax.mk_icomb)
