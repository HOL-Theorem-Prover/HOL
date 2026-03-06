## `mk_thy_const`

``` hol4
Term.mk_thy_const : {Thy:string, Name:string, Ty:hol_type} -> term
```

------------------------------------------------------------------------

Constructs a constant.

If `n` is a string that has been previously declared to be a constant
with type `ty` in theory `thy`, and `ty1` is an instance of `ty`, then
`mk_thy_const{Name=n, Thy=thy, Ty=ty1}` returns the specified instance
of the constant.

(A type `ty1` is an 'instance' of a type `ty2` when `match_type ty2 ty1`
does not fail.)

### Failure

Fails if `n` is not the name of a constant in theory `thy`, if `thy` is
not in the ancestry of the current theory, or if `ty1` is not an
instance of `ty`.

### Example

``` hol4
   - mk_thy_const {Name="T", Thy="bool", Ty=bool};
   > val it = `T` : term

   - try mk_thy_const {Name = "bar", Thy="foo", Ty=bool};
   Exception raised at Term.mk_thy_const:
   "foo$bar" not found
```

### See also

[`Term.dest_thy_const`](#Term.dest_thy_const),
[`Term.mk_const`](#Term.mk_const),
[`Term.dest_const`](#Term.dest_const),
[`Term.is_const`](#Term.is_const), [`Term.mk_var`](#Term.mk_var),
[`Term.mk_comb`](#Term.mk_comb), [`Term.mk_abs`](#Term.mk_abs),
[`Type.match_type`](#Type.match_type)
