## `parse_in_context`

``` hol4
Parse.parse_in_context : term list -> term quotation -> term
```

------------------------------------------------------------------------

Parses a quotation into a term, using the terms as typing context.

Where the `Term` function parses a quotation in isolation of all
possible contexts (except inasmuch as the global grammar provides a form
of context), this function uses the additional parameter, a list of
terms, to help in giving variables in the quotation types.

Thus, `` Term`x` `` will either guess the type ``` ``:'a`` ``` for this
quotation, or refuse to parse it at all, depending on the value of the
`guessing_tyvars` flag. The `parse_in_context` function, in contrast,
will attempt to find a type for `x` from the list of free variables.

If the quotation already provides enough context in itself to determine
a type for a variable, then the context is not consulted, and a
conflicting type there for a given variable is ignored.

### Failure

Fails if the quotation doesn't make syntactic sense, or if the
assignment of context types to otherwise unconstrained variables in the
quotation causes overloading resolution to fail. The latter would happen
if the variable `x` was given boolean type in the context, if `+` was
overloaded to be over either `:num` or `:int`, and if the quotation was
`x + y`.

### Example

``` hol4
   << There should be an example here >>
```

Used in many of the `Q` module's variants of the standard tactics in
order to have a goal provide contextual information to the parsing of
arguments to tactics.

### See also

[`Parse.Term`](#Parse.Term)
