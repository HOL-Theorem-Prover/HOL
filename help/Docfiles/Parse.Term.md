## `Term` {#Parse.Term}


```
Parse.Term : term quotation -> term
```



Parses a quotation into a term value.


The parsing process for terms divides into four distinct phases.

The first phase converts the quotation argument into abstract syntax,
a relatively simple parse tree datatype, with the following datatype
definition (from `Absyn`):
    
       datatype vstruct
           = VAQ    of term
           | VIDENT of string
           | VPAIR  of vstruct * vstruct
           | VTYPED of vstruct * pretype
       datatype absyn
           = AQ    of term
           | IDENT of string
           | APP   of absyn * absyn
           | LAM   of vstruct * absyn
           | TYPED of absyn * pretype
    
This phase of parsing is concerned with the treatment of the
rawest concrete syntax.  It has no notion of whether or not a term
corresponds to a constant or a variable, so all `preterm` leaves are
ultimately either `IDENT`s or `AQ`s (anti-quotations).

This first phase converts infixes, mixfixes and all the other
categories of syntactic rule from the global grammar into simple
structures built up using `APP`.  For example, `` `x op y` `` (where `op`
is an infix) will turn into
    
       APP(APP(IDENT "op", IDENT "x"), IDENT "y")
    
and `` `tok1 x tok2 y` `` (where `tok1 _ tok2` has been declared as a
`Prefix` form for the term `f`) will turn into
    
       APP(APP(IDENT "f", IDENT "x"), IDENT "y")
    
The special syntaxes for “let” and record expressions are also
handled at this stage.  For more details on how this is done see the
reference entry for `Absyn`, which function can be used in
isolation to see what is done at this phase.

The second phase of parsing consists of the resolution of names,
identifying what were just `VAR`s as constants or genuine variables
(whether free or bound).  This phase also annotates all leaves of the
data structure (given in the entry for `Preterm`) with type
information.

The third phase of parsing works over the `Preterm` datatype and does
type-checking, though ignoring overloaded values.  The datatype being
operated over uses reference variables to allow for efficiency, and
the type-checking is done “in place”.  If type-checking is
successful, the resulting value has consistent type annotations.

The final phase of parsing resolves overloaded constants.  The
type-checking done to this point may completely determine which choice
of overloaded constant is appropriate, but if not, the choice may
still be completely determined by the interaction of the possible
types for the overloaded possibilities.

Finally, depending on the value of the global flags `guessing_tyvars`
and `guessing_overloads`, the parser will make choices about how to
resolve any remaining ambiguities.

The parsing process is entirely driven by the global grammar.  This
value can be inspected with the `term_grammar` function.

### Failure

All over place, and for all sorts of reasons.


Turns strings into terms.

### See also

[`Parse.Absyn`](#Parse.Absyn), [`Parse.overload_on`](#Parse.overload_on), [`Parse.term_grammar`](#Parse.term_grammar)

