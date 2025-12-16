## `Absyn`

``` hol4
Parse.Absyn : term quotation -> Absyn.absyn
```

------------------------------------------------------------------------

Implements the first phase of term parsing; the removal of special
syntax.

`Absyn` takes a quotation and parses it into an abstract syntax tree of
type `absyn`, using the current term and type grammars. This phase of
parsing is unconcerned with types, and will happily parse meaningless
expressions that are syntactically valid.

### Example

`Absyn` will parse the expression `` `let x = e1 in e2` `` into

``` hol4
   APP(APP(IDENT "LET", LAM(VIDENT "x", IDENT "e2")), IDENT "e1")
```

The record syntax `` `rec.fld1` `` is converted into something of the
form

``` hol4
   APP(IDENT "....fld1", IDENT "rec")
```

where the dots will actually be equal to the value of
`GrammarSpecials.recsel_special` (a string).

### Failure

Fails if the quotation has a syntax error.

`Absyn` is not often used, but may be handy for implementing some weird
and wonderful concrete syntax that surpasses the functionality of the
HOL parser.

### See also

[`Parse.Term`](#Parse.Term), [`Parse.term_grammar`](#Parse.term_grammar)
