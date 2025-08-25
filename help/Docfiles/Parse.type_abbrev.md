## `type_abbrev`

``` hol4
Parse.type_abbrev : string * hol_type -> unit
```

------------------------------------------------------------------------

Establishes a type abbreviation.

A call to `type_abbrev(s,ty)` sets up a type abbreviation that will
cause the parser to treat the string `s` as a synonym for the type `ty`.
Moreover, if `ty` includes any type variables, then the abbreviation is
treated as a type operator taking as many parameters as appear in `ty`.
The order of the parameters will be the alphabetic ordering of the type
variables' names.

Abbreviations work at the level of the names of type operators. It is
thus possible to link a binary infix to an operator that is in turn an
abbreviation.

### Failure

Fails if the given type is just a type variable.

### Example

This is a simple abbreviation.

``` hol4
   > type_abbrev ("set", ``:'a -> bool``);
   val it = () : unit

   > ``:num set``;
   val it = ``:num -> bool`` : hol_type
```

Here, the abbreviation is set up and provided with its own infix symbol.

``` hol4
   - type_abbrev ("rfunc", ``:'b -> 'a``);
   > val it = () : unit

   - add_infix_type {Assoc = RIGHT, Name = "rfunc",
                     ParseName = SOME "<-", Prec = 50};
   > val it = () : unit

   - ``:'a <- bool``;
   > val it = ``:bool -> 'a`` : hol_type

   - dest_thy_type it;
   > val it = {Args = [``:bool``, ``:'a``], Thy = "min", Tyop = "fun"} :
      {Args : hol_type list, Thy : string, Tyop : string}
```

### Comments

As is common with most of the parsing and printing functions, there is a
companion `temp_type_abbrev` function that does not cause the
abbreviation effect to persist when the theory is exported. As the
examples show, this entrypoint does not affect the pretty-printing of
types. If printing of abbreviations is desired as well as parsing, the
entrypoint `type_abbrev_pp` should be used.

### See also

[`Parse.add_infix_type`](#Parse.add_infix_type),
[`Parse.disable_tyabbrev_printing`](#Parse.disable_tyabbrev_printing),
[`Parse.remove_type_abbrev`](#Parse.remove_type_abbrev),
[`Parse.thytype_abbrev`](#Parse.thytype_abbrev),
[`Parse.type_abbrev_pp`](#Parse.type_abbrev_pp)
