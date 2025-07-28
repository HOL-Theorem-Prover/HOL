## `remove_type_abbrev` {#Parse.remove_type_abbrev}


```
remove_type_abbrev : string -> unit
```



Remove a type abbreviation from the type grammar.


A call to `remove_type_abbrev s` removes any type abbreviations keyed
on string `s`. As with other functions affecting the global grammar,
there is a companion function, `temp_remove_type_abbrev`, which
affects the grammar but does not cause the effect to be replayed in
descendant theories.

If the string `s` is not a qualified name (of the form `"thy$name"`),
then all type abbreviations with base name `s` are removed. If `s`
does have a qualified name, then only a type abbreviation of that name
and theory will be removed (if such exists).

### Failure

Fails if the given string is a malformed qualified identifier (e.g.,
`foo$$`). If the given name is syntactically valid, but there are no
abbreviations keyed to the given name, a call to `remove_type_abbrev`
will silently do nothing.

### Example

The standard theory context (where `pred_set` is loaded), includes an
abbreviation mapping ``` ``:'a set`` ``` to ``` ``:'a -> bool`` ```. It doesn’t
print the abbreviated form back to the user, because its printing has
been disabled with `disable_tyabbrev_printing`.

    
       > ``:'a set``;
       val it = ``:'a -> bool`` : hol_type
    
       > remove_type_abbrev "set";
       val it = (): unit
    
       > ``:'a set``;
       Exception- HOL_ERR ...
    

### See also

[`Parse.disable_tyabbrev_printing`](#Parse.disable_tyabbrev_printing), [`Parse.type_abbrev`](#Parse.type_abbrev)

