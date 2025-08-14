## `dest_thy_type`

``` hol4
Type.dest_thy_type
    : hol_type -> {Thy:string, Tyop:string,
                   Args:hol_type list}
```

------------------------------------------------------------------------

Breaks apart a type (other than a variable type).

If `ty` is an application of a type operator `Tyop`, which was declared
in theory `Thy`, to a list of types `Args`, then `dest_thy_type ty`
returns `{Tyop,Thy,Args}`.

### Failure

Fails if `ty` is a type variable.

### Example

``` hol4
- dest_thy_type “:'a -> bool”;
> val it = {Args = [“:α”, “:bool”], Thy = "min", Tyop = "fun"} :

- try dest_thy_type alpha;

Exception raised at Type.dest_thy_type:
```

### See also

[`Type.mk_thy_type`](#Type.mk_thy_type),
[`Type.dest_type`](#Type.dest_type), [`Type.mk_type`](#Type.mk_type),
[`Term.mk_thy_const`](#Term.mk_thy_const)
