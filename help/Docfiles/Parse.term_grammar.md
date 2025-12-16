## `term_grammar`

``` hol4
Parse.term_grammar : unit -> term_grammar.grammar
```

------------------------------------------------------------------------

Returns the current global term grammar.

### Failure

Never fails.

### Comments

There is a pretty-printer installed in the interactive system so that
term grammar values are presented nicely. The global term grammar is
passed as a parameter to the `Term` parsing function in the `Parse`
structure, and also drives the installed term and theorem
pretty-printers.

### See also

[`Parse.parse_from_grammars`](#Parse.parse_from_grammars),
[`Parse.print_from_grammars`](#Parse.print_from_grammars),
[`Parse.temp_set_grammars`](#Parse.temp_set_grammars),
[`Parse.Term`](#Parse.Term)
