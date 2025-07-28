## `print_from_grammars` {#Parse.print_from_grammars}


```
print_from_grammars :
  (type_grammar.grammar * term_grammar.grammar) ->
  (hol_type Parse.pprinter * term Parse.pprinter)
```



Returns printing functions based on the supplied grammars.


When given a pair consisting of a type and term grammar (such a pair
is exported with every theory, under the name `<thy>_grammars`), this
function returns printing functions that use those grammars to render
terms and types using the system’s standard pretty-printing stream
type.

### Failure

Never fails.

### Example

With `arithmeticTheory` loaded, arithmetic expressions and numerals
print pleasingly:
    
       - load "arithmeticTheory";
       > val it = () : unit
    
       - ``3 + x * 4``;
       > val it = ``3 + x * 4`` : term
    
The printing of these terms is controlled by the global grammar, which
is augmented when the theory of arithmetic is loaded.  Printing
functions based on the grammar of the base theory `bool` can be
defined:
    
       > val (typepp, termpp) = print_from_grammars bool_grammars;
       val termpp = fn : term Parse.pprinter
       val typepp = fn : hol_type Parse.pprinter
    
These functions can then be used to print arithmetic terms (note that
neither the global parser nor printer are disturbed by this activity),
using the `Portable.pprint` function
(or `Lib.ppstring`, which returns a string):
    
       > Portable.pprint termpp ``3 + x * 4``;
       arithmetic$+
         (arithmetic$NUMERAL
            (arithmetic$BIT1 (arithmetic$BIT1 arithmetic$ZERO)))
         (arithmetic$* x
            (arithmetic$NUMERAL
               (arithmetic$BIT2 (arithmetic$BIT1 arithmetic$ZERO))))
       > val it = () : unit
    
Not only have the fixities of `+` and `*` been ignored, but the
constants in the term, belonging to `arithmeticTheory`, are all
printed in “long identifier” form because the grammars from
`boolTheory` don’t know about them.


Printing terms with early grammars such as `bool_grammars` can remove
layers of potentially confusing pretty-printing, including complicated
concrete syntax and overloading, and even the underlying
representation of numerals.

### See also

[`Parse.parse_from_grammars`](#Parse.parse_from_grammars), [`Parse.print_term_by_grammar`](#Parse.print_term_by_grammar), [`Parse.Term`](#Parse.Term), [`Portable.pprint`](#Portable.pprint), [`Lib.ppstring`](#Lib.ppstring)

