## `disable_tyabbrev_printing`

``` hol4
Parse.disable_tyabbrev_printing : string -> unit
```

------------------------------------------------------------------------

Disables the printing of a type abbreviation.

A call to `disable_tyabbrev_printing s` causes type abbreviations
mapping the string `s` to some type expansion not to be printed when an
instance of the type expansion is seen.

If the string `s` is not a qualified name (of the form `"thy$name"`),
then all type abbreviations with base name `s` are disabled. If `s` does
have a qualified name, then only a type abbreviation of that name and
theory will be disabled (if such exists).

### Failure

Fails if the given string is a malformed qualified identifier (e.g.,
`foo$$`). If the given name is syntactically valid, but there are no
abbreviations keyed to the given name, a call to
`disable_tyabbrev_printing` will silently do nothing.

### Example

``` hol4
- type_abbrev("LIST", ``:'a list``)
> val it = () : unit

- ``:num list``;
> val it = ``:num LIST`` : hol_type

- disable_tyabbrev_printing "LIST";
> val it = () : unit

- ``:num LIST``;
> val it = ``:num list`` : hol_type
```

### Comments

When a type-abbreviation is established with the function `type_abbrev`,
this alters both parsing and printing: when the new abbreviation appears
in input the type parser will translate away the abbreviation.
Similarly, when an instance of the abbreviation appears in a type that
the printer is to output, it will replace the instance with the
abbreviation.

This is generally the appropriate behaviour. However, there is are a
number of useful abbreviations where reversing parsing when printing is
not so useful. For example, the abbreviation mapping `'a set` to
`'a -> bool` is convenient, but it would be a mistake having it print
because types such as that of conjunction would print as

``` hol4
   (/\) : bool -> bool set
```

which is rather confusing.

As with other printing and parsing functions, there is a version of this
function, `temp_disable_tyabbrev_printing` that does not cause its
effect to persist with an exported theory.

### See also

[`Parse.remove_type_abbrev`](#Parse.remove_type_abbrev),
[`Parse.type_abbrev`](#Parse.type_abbrev)
