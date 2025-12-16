## `add_strliteral_form`

``` hol4
Parse.add_strliteral_form : {inj:term, ldelim:string} -> unit
```

------------------------------------------------------------------------

Adds interpretation for string literal syntaxes

If `ld` is a valid left delimiter, with corresponding right delimiter
`rd`, then a call to `add_strliteral_form{inj=t,ldelim=ld}` causes the
parser and pretty-printer to treat string literals delimited by `ld` and
`rd` as occurrences of the term `inj` applied to the given HOL value
(which will be of `string` type).

If the given `ld`-`rd` pair is already associated with an injector, then
the parsing process will resolve the ambiguity with the standard
overloading resolution method. In particular, note that the standard
double quotation mark (ASCII character 34, `"`) is associated with the
"null" injector, which takes string literals into the `string` type.
Other injectors can be associated with this delimiter pair.

The other valid delimiter pairs are double guillemets (`«...»`, U+00AB
and U+00BB) and single guillemets (`‹...›`, U+2039 and U+203A).

### Failure

Fails if the `ldelim` field does not correspond to a valid left
delimiter, or if the HOL type of the `inj` field is not `:string->X` for
some type `X`.

### Example

If we have established a new type of deeply embedded terms with
variables, constants and binary applications:

``` hol4
   Datatype`tm = V string | Cst string | App tm tm`;
```

then we can overload the usual double-quoted string literals to also be
applications of the `V` constructor:

``` hol4
   > add_strliteral_form {inj=``V``, ldelim="\""};
   > ``App (V "foo") (App "bar" "baz")``;
   val it = “App "foo" (App "bar" "baz")”: term
```

where all the string literals in the output are actually applications of
`V` to a real literal.

We can further choose to have constants printed with enclosing `«...»`
by:

``` hol4
   > add_strliteral_form {inj=``Cst``, ldelim="«"};
   > ``App "foo" (Cst "bar")``;
   val it = “App "foo" «bar»”: term
```

Note that in this situation, use of the double guillemets is
unambiguous, but a bare string literal is strictly ambiguous (the
default is to prefer the core string type):

``` hol4
   > type_of “«foo»”;
   val it = “:tm”: hol_type

   > type_of “"foo"”;
   <<HOL message: more than one resolution of overloading was possible>>
   val it = “:string”: hol_type
```

### Comments

This facility is analogous to the way in which numerals can be seen to
inhabit types other than just `:num`. As with other parsing facilities
there is a temporary form `temp_add_strliteral_form`, which does not
cause the change to the grammar to persist to descendant theories.

The effect of adding a new string literal form can be reversed by
parallel `remove_string_literal_form` and
`temp_remove_string_literal_form` functions.

### See also

[`Parse.add_numeral_form`](#Parse.add_numeral_form)
