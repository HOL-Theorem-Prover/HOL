## `type_abbrev_pp`

``` hol4
Parse.type_abbrev_pp : string * hol_type -> unit
```

------------------------------------------------------------------------

Installs type abbreviation affecting parsing and printing.

As with `type_abbrev(s,ty)`, a call to `type_abbrev_pp(s,ty)` sets up
the string `s` to be an abbrevation for the type `ty` when types are
parsed. In addition, it causes the type pretty-printer to prefer the
abbreviation when it comes to print types that match the implicit
pattern specified by `ty` (which may include type variables).

### Failure

Fails if the provided type is a single type variable.

### Example

``` hol4
   > type_abbrev_pp ("foo", ``:num -> 'a # num``);
   val it = () : unit

   > ``:bool foo``;
   val it = ``:bool foo``: hol_type

   > dest_thy_type it;
   val it = {Args = [``:num``, ``:bool # num``],
             Thy = "min", Tyop = "fun"}:
      {Args: hol_type list, Thy: string, Tyop: string}
```

### See also

[`Parse.type_abbrev`](#Parse.type_abbrev)
