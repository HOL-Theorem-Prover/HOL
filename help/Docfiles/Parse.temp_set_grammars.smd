## `temp_set_grammars`

``` hol4
Parse.temp_set_grammars : type_grammar.grammar * term_grammar.grammar -> unit
```

------------------------------------------------------------------------

Sets the global type and term grammars.

HOL uses two global grammars to control the parsing and printing of term
and type values. These can be adjusted in a controlled way with
functions such as `add_rule` and `overload_on`. By using just these
standard functions, the system is able to export theories in such a way
that changes to grammars persist from session to session.

Nonetheless it is occasionally useful to set grammar values directly.
This change can't be made to persist, but will affect the current
session.

### Failure

Never fails.

### See also

[`Parse.current_grammars`](#Parse.current_grammars),
[`Parse.add_rule`](#Parse.add_rule),
[`Parse.overload_on`](#Parse.overload_on),
[`Parse.parse_from_grammars`](#Parse.parse_from_grammars),
[`Parse.print_from_grammars`](#Parse.print_from_grammars),
[`Parse.Term`](#Parse.Term)
