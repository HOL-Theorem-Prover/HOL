## `declare_monad`

``` hol4
monadsyntax.declare_monad :
  string * { bind : term, unit : term, ignorebind : term option,
             choice : term option, fail : term option, guard : term option }
    ->
  unit
```

------------------------------------------------------------------------

Declares a monad type for which the do/od syntax can be used.

A call to `declare_monad(mname, minfo)` alters the internal "monad
database" so that a subsequent call to `enable_monad mname` will cause
do/od syntax to try to use the terms in `minfo` as interpretations of
that syntax. The only compulsory values are the `unit` and `bind`
values, which should have types conforming to the pattern `:α M` and
`:α -> β M` respectively. For example, the list monad would have `M`
instantiated by the pattern `:_ list`, while the reader monad would have
`M` instantiated by the pattern `:'env -> _`.

The `ignorebind` field allows the user to provide a specific constant to
interpret a `bind` where the second argument ignores the value. If this
is not provided, then syntax such as `do M1; M2; od` will be interpreted
as `bind M1 (K M2)`, where `K` is the constant combinator.

The remaining fields are used when the monad has a notion of failure.
For example, the option monad uses `NONE` as the appropriate value for
`fail`. The `choice` term should be of type `:α M -> α M -> α M`, and
should return the first value if it is not a failure, or otherwise use
the second argument. The supported syntax for `choice` is `++`.

Finally, the `guard` field should be a term of type `:bool -> unit M`.
It is rendered as `assert b` with `b` a boolean value. If `b` is true,
the monad "returns" the unit value; if `b` is false the monad fails.

The information declared with a call to `declare_monad` is exported with
the current theory and is thus available to descendent theories.

### Failure

Never fails. However, the terms present in the monad-information record
must have appropriate types if strange type-checking errors on
subsequent uses of the do/od syntax are to be avoided.

### Example

A set monad could be declared:

``` hol4
> declare_monad("set", {
    unit = “λa. {a}”, bind = “λs f. BIGUNION (IMAGE f s)”,
    ignorebind = NONE,
    fail = SOME “{}”, guard = SOME “λb. if b then {()} else {}”,
    choice = SOME “$UNION”
  });
```

### Comments

This function does not even care if the constants have the right
respective types; it certainly doesn't care if the constants satisfy the
monadic axioms.

### See also

[`monadsyntax.all_monads`](#monadsyntax.all_monads),
[`monadsyntax.enable_monad`](#monadsyntax.enable_monad)
