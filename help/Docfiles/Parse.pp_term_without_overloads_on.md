## `pp_term_without_overloads_on`

``` hol4
Parse.pp_term_without_overloads_on : string list -> term PP.pprinter
```

------------------------------------------------------------------------

Printing function for terms without using overload mappings of certain
tokens.

The call `pp_term_without_overloads_on ls` returns a printing function
to print terms without using any overload mappings of the tokens in
`ls`, using the system's standard pretty-printing stream type.

### Example

``` hol4
 > val termpp = pp_term_without_overloads_on ["+"];
 val termpp = fn: term Parse.pprinter
 > val _ = Portable.pprint termpp ``x + y`` ;
 arithmetic$+ x y
 val it = (): unit
```

### Failure

Should never fail.

### See also

[`Parse.pp_term_without_overloads`](#Parse.pp_term_without_overloads),
[`Parse.print_term_without_overloads_on`](#Parse.print_term_without_overloads_on),
[`Parse.term_without_overloads_on_to_string`](#Parse.term_without_overloads_on_to_string),
[`Parse.print_from_grammars`](#Parse.print_from_grammars)
