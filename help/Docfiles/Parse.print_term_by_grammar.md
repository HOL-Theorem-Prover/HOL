## `print_term_by_grammar`

``` hol4
Parse.print_term_by_grammar :
  (type_grammar.grammar * term_grammar.grammar) -> term -> unit
```

------------------------------------------------------------------------

Prints a term to standard out, using grammars to specify how.

Where `print_term` uses the (implicit) global grammars to control the
printing of its term argument, the `print_term_by_grammar` uses
user-supplied grammars. These can control the printing of concrete
syntax (operator fixities and precedency) and the degree of constant
overloading.

### Failure

Never fails.

### See also

[`Parse.print_from_grammars`](#Parse.print_from_grammars)
