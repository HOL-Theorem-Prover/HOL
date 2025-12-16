## `inst`

``` hol4
Term.inst : (hol_type,hol_type)subst -> term -> term
```

------------------------------------------------------------------------

Performs type instantiations in a term.

The function `inst` should be used as follows:

``` hol4
   inst [{redex_1, residue_1},...,{redex_n, residue_n}] tm
```

where each 'redex' is a `hol_type` variable, and each 'residue' is a
`hol_type` and `tm` a term to be type-instantiated. This call will
replace each occurrence of a `redex` in `tm` by its associated
`residue`. Replacement is done in parallel, i.e., once a `redex` has
been replaced by its `residue`, at some place in the term, that
`residue` at that place will not itself be replaced in the current call.
Bound term variables may be renamed in order to preserve the term
structure.

### Failure

Never fails. A `redex` that is not a variable is simply ignored.

### Example

``` hol4
- show_types := true;
> val it = () : unit

- inst [alpha |-> Type`:num`] (Term`(x:'a) = (x:'a)`)
> val it = `(x :num) = x` : term

- inst [bool |-> Type`:num`] (Term`x:bool`);
> val it = `(x :bool)` : term

- inst [alpha |-> bool] (mk_abs(Term`x:bool`,Term`x:'a`))
> val it = `\(x' :bool). (x :bool)` : term
```

### See also

[`Type.type_subst`](#Type.type_subst), [`Lib.|->`](#Lib..GZKQ4)
