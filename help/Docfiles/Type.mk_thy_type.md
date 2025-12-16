## `mk_thy_type`

``` hol4
Type.mk_thy_type
       : {Thy:string, Tyop:string, Args:hol_type list} -> hol_type
```

------------------------------------------------------------------------

Constructs a type.

If `s` is a string that has been previously declared to be a type with
arity type `n` in theory `thy`, and the length of `tyl` is equal to `n`,
then `mk_thy_type{Tyop=s, Thy=thy, Args=tyl}` returns the requested
compound type.

### Failure

Fails if `s` is not the name of a type in theory `thy`, if `thy` is not
in the ancestry of the current theory, or if `n` is not the length of
`tyl`.

### Example

``` hol4
- mk_thy_type {Tyop="fun", Thy="min", Args = [alpha,bool]};
> val it = `:'a -> bool` : hol_type

- try mk_thy_type {Tyop="bar", Thy="foo", Args = []};

Exception raised at Type.mk_thy_type:
"foo$bar" not found
```

### Comments

In general, `mk_thy_type` is to be preferred over `mk_type` because HOL
provides a fresh namespace for each theory (`mk_type` is a holdover from
a time when there was only one namespace shared by all theories).

### See also

[`Type.mk_type`](#Type.mk_type),
[`Type.dest_thy_type`](#Type.dest_thy_type),
[`Term.mk_const`](#Term.mk_const),
[`Term.mk_thy_const`](#Term.mk_thy_const)
