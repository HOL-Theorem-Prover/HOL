## `thy_addon`

``` hol4
Theory.type thy_addon
```

------------------------------------------------------------------------

Type of theory additions.

The type abbreviation `thy_addon`, declared as

``` hol4
   type thy_addon = {sig_ps : unit PP.pprinter option,
                     struct_ps : unit PP.pprinter option}
```

packages up the arguments to `adjoin_to_theory`. The `sig_ps` argument
is an optional prettyprinter, which will be invoked when the theory
signature file is written. The `struct_ps` argument is an optional
prettyprinter invoked when the theory structure file is written.

The `unit` type parameter in both cases simply means that the
pretty-printers won't be passed any extra information when invoked.

### See also

[`Theory.adjoin_to_theory`](#Theory.adjoin_to_theory)
