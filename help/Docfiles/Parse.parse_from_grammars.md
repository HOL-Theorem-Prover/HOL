## `parse_from_grammars`

``` hol4
Parse.parse_from_grammars :
  (type_grammar.grammar * term_grammar.grammar) ->
  ((hol_type frag list -> hol_type) * (term frag list -> term))
```

------------------------------------------------------------------------

Returns parsing functions based on the supplied grammars.

When given a pair consisting of a type and a term grammar, this function
returns parsing functions that use those grammars to turn strings
(strictly, quotations) into types and terms respectively.

### Failure

Can't fail immediately. However, when the precedence matrix for the term
parser is built on first application of the term parser, this may
generate precedence conflict errors depending on the rules in the
grammar.

### Example

First the user loads `arithmeticTheory` to augment the built-in grammar
with the ability to lex numerals and deal with symbols such as `+` and
`-`:

``` hol4
   - load "arithmeticTheory";
   > val it = () : unit
   - val t = Term`2 + 3`;
   > val t = `2 + 3` : term
```

Then the `parse_from_grammars` function is used to make the values
`Type` and `Term` use the grammar present in the simpler theory of
booleans. Using this function fails to parse numerals or even the `+`
infix:

``` hol4
   - val (Type,Term) = parse_from_grammars boolTheory.bool_grammars;
   > val Type = fn : hol_type frag list -> hol_type
     val Term = fn : term frag list -> term
   - Term`2 + 3`;
   <<HOL message: No numerals currently allowed.>>
   ! Uncaught exception:
   ! HOL_ERR <poly>
   - Term`x + y`;
   <<HOL message: inventing new type variable names: 'a, 'b.>>
   > val it = `x $+ y` : term
```

But, as the last example above also demonstrates, the installed
pretty-printer is still dependent on the global grammar, and the global
value of `Term` can still be accessed through the `Parse` structure:

``` hol4
   - t;
   > val it = `2 + 3` : term

   - Parse.Term`2 + 3`;
   > val it = `2 + 3` : term
```

This function is used to ensure that library code has access to a term
parser that is a known quantity. In particular, it is not good form to
have library code that depends on the default parsers `Term` and `Type`.
When the library is loaded, which may happen at any stage, these global
values may be such that the parsing causes quite unexpected results or
failures.

### See also

[`Parse.add_rule`](#Parse.add_rule),
[`Parse.print_from_grammars`](#Parse.print_from_grammars),
[`Parse.Term`](#Parse.Term)
