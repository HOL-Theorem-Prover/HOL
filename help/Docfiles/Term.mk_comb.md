## `mk_comb`

``` hol4
Term.mk_comb : term * term -> term
```

------------------------------------------------------------------------

Constructs a combination (function application).

`mk_comb (t1,t2)` returns the combination `t1 t2`.

### Failure

Fails if `t1` does not have a function type, or if `t1` has a function
type, but its domain does not equal the type of `t2`.

### Example

``` hol4
   - mk_comb (neg_tm,T);

   > val it = `~T` : term

   - mk_comb(T, T) handle e => Raise e;

   Exception raised at Term.mk_comb:
   incompatible types
```

### See also

[`Term.dest_comb`](#Term.dest_comb), [`Term.is_comb`](#Term.is_comb),
[`Term.list_mk_comb`](#Term.list_mk_comb),
[`Term.mk_var`](#Term.mk_var), [`Term.mk_const`](#Term.mk_const),
[`Term.mk_abs`](#Term.mk_abs)
