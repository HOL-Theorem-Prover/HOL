## `enable_monadsyntax`

``` hol4
monadsyntax.enable_monadsyntax : unit -> unit
```

------------------------------------------------------------------------

Enables parsing and printing of monadic do/od syntax.

A call to `enable_monadsyntax()` alters the parser and pretty-printer to
support the do/od syntax for writing monadic values. This call should be
followed by calls to `enable_monad` (or `weak_enable_monad`) so that the
do/od syntax can be linked to actual monadic types.

### Failure

Never fails.

### Example

This first example gives a clear demonstration of the nature of the
syntactic translation that the monad syntax implements because there is
no specific enabled monad for the syntax to map to:

``` hol4
   > monadsyntax.enable_monadsyntax();
   val it = () : unit

   > “do M1 ; M2; od”;
   val it = “monad_unitbind M1 M2” : term;

   > “do v <- M1; w <- M2 v 3; return (v + w); od”;
   val it = “monad_bind M1 (λv. monad_bind (M2 v 3) (λw. return (v + w)))”
            : term
```

The `monad_bind`, `monad_unitbind` and `return` terms above are
variables that would be instantiated with the appropriate terms given
the available choices of enabled monads.

### See also

[`monadsyntax.all_monads`](#monadsyntax.all_monads),
[`monadsyntax.enable_monad`](#monadsyntax.enable_monad)
