## `deprecate_int`

``` hol4
intLib.deprecate_int : unit -> unit
```

------------------------------------------------------------------------

Makes the parser never consider integers as a numeric possibility.

Calling `deprecate_int()` causes the parser to remove all of the
standard numeric constants over the integers from consideration. In
addition to the standard operators (`+`, `-`, `*` and others), this also
affects numerals; after the call to `deprecate_int` these will never be
parsed as integers.

This function, by affecting the global grammar, also affects the
behaviour of the pretty-printer. A term that includes affected constants
will print with those constants in "fully qualified form", typically as
`integer$op`, and numerals will print with a trailing `i`.
(Incidentally, the parser will always read integer terms if they are
presented to it in this form.)

### Failure

Never fails.

### Example

First we load the integer library, ensuring that integers and natural
numbers both are possible when we type numeric expressions:

``` hol4
   - load "intLib";
   > val it = () : unit
```

Then, when we type such an expression, we're warned that this is
strictly ambiguous, and a type is silently chosen for us:

``` hol4
   - val t = ``2 + x``;
   <<HOL message: more than one resolution of overloading was possible>>
   > val t = ``2 + x`` : term

   - type_of t;
   > val it = ``:int`` : hol_type
```

Now we can use `deprecate_int` to stop this happening, and make sure
that we just get natural numbers:

``` hol4
   - intLib.deprecate_int();
   > val it = () : unit

   - ``2 + x``;
   > val it = ``2 + x`` : term

   - type_of it;
   > val it = ``:num`` : hol_type
```

The term we started out with is now printed in rather ugly fashion:

``` hol4
   - t;
   > val it = ``integer$int_add 2i x`` : term
```

### Comments

If one wishes to simply prefer the natural numbers, say, to the
integers, and yet still retain integers as a possibility, use
`numLib.prefer_num` rather than this function. This function only brings
about a "temporary" effect; it does not cause the change to be exported
with the current theory.

### See also

[`intLib.prefer_int`](#intLib.prefer_int)
