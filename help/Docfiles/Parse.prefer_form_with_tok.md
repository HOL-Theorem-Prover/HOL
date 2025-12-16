## `prefer_form_with_tok`

``` hol4
Parse.prefer_form_with_tok : {term_name : string, tok : string} -> unit
```

------------------------------------------------------------------------

Sets a grammar rule's preferred flag, causing it to be preferentially
printed.

A call to `prefer_form_with_tok` causes the parsing/pretty-printing rule
specified by the `term_name`-`tok` combination to be the preferred rule
for pretty-printing purposes. This change affects the global grammar.

### Failure

Never fails.

### Example

Imagine that one wants to use an infix `"U"` to stand for the `"UNION"`
term. This could be done as follows:

``` hol4
   > set_mapped_fixity {term_name = "UNION", fixity = Infixl 500,
                        tok = "U"};
   val it = () : unit

   > ``s U t``;
   val it = ``s U t`` : term

   > dest_term it;
   val it = COMB(``$UNION s``, ``t``) : lambda
```

Having made this change, one might prefer to see the form with `UNION`
printed:

``` hol4
   > prefer_form_with_tok {term_name = "UNION", tok = "UNION"};
   val it = () : unit

   > ``s U t``;
   val it = ``s UNION t`` : term
```

### Comments

As the example above demonstrates, using this function does not affect
the parser at all.

There is a companion `temp_prefer_form_with_tok` function, which has the
same effect on the global grammar, but which does not cause this effect
to persist when the current theory is exported.
