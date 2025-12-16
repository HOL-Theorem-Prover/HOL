## `enable_monad`

``` hol4
monadsyntax.enable_monad : string -> unit
```

------------------------------------------------------------------------

Enables a particular monadic type for use with do/od syntax.

A call to `enable_monad mname`, where `mname` is an SML value of type
`string`, enables the stored information about monad `mname` to govern
the interpretation of the do/od syntax. If multiple monads are enabled,
normal overloading resolution will decide between them.

### Failure

Fails if `mname` is not the name of a stored monad in the internal
database (which can be examined with a call to
`monadsyntax.all_monads()`. Will have little effect if monad syntax has
not been generally enabled with a prior call to `enable_monadsyntax`.

### Example

In what follows, `oHD` is the function which maps a non-empty list to
`SOME` applied to that list's first element, and the empty list to
`NONE`. The `++` is the monad choice function (the option monad has a
notion of failure). Thus, the function below that is bound to SML
variable `f` is one that either increments the first element of a list
and returns that value, or returns 0.

``` hol4
> enable_monadsyntax(); enable_monad "option";
val it = () : unit
val it = () : unit

> val f = “λl. do x <- oHD l; return (x + 1); od ++ return 0”
val f = “λl. do x <- oHD l; SOME (x + 1); od ++ SOME 0” : term

> EVAL “^f [3; 10]”;
val it = ⊢ (λl. do x <- oHD l; SOME (x + 1) od ⧺ SOME 0) [3; 10] = SOME 4:
   thm

> EVAL “^f []”;
val it = ⊢ (λl. do x <- oHD l; SOME (x + 1) od ⧺ SOME 0) [] = SOME 0: thm
```

Note how the `return` keyword is not printed as such by the parser; it
would be too confusing if all occurrences of common functions such as
`SOME` were printed as `return`.

### Comments

As with other parsing and printing functions, there is a
`temp_enable_monad` function whose changes to the parser and printer do
not persist to descendent theories.

### See also

[`monadsyntax.all_monads`](#monadsyntax.all_monads),
[`monadsyntax.declare_monad`](#monadsyntax.declare_monad),
[`monadsyntax.enable_monadsyntax`](#monadsyntax.enable_monadsyntax)
