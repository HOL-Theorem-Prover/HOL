## `set_known_constants`

``` hol4
Parse.set_known_constants : string list -> unit
```

------------------------------------------------------------------------

Specifies the list of names that should be parsed as constants.

One of the final phases of parsing is the resolution of free names in
putative terms as either variables, constants or overloaded constants.
If such a free name is not overloaded, then the list of known constants
is consulted to determine whether or not to treat it as a constant. If
the name is not present in the list, then it will be treated as a free
variable.

### Failure

Never fails. If a name is specified in the list of constants that is not
in fact a constant, a warning message is printed, and that name is
ignored.

### Example

``` hol4
- known_constants();
> val it =
    ["bool_case", "ARB", "TYPE_DEFINITION", "ONTO", "ONE_ONE", "COND",
     "LET", "?!", "~", "F", "\\/", "/\\", "!", "T", "?", "@",
     "==>", "="]
    : string list
- Term`p /\ q`;
> val it = `p /\ q` : term
- set_known_constants (Lib.subtract (known_constants()) ["/\\"]);
> val it = () : unit
- Term`p /\ q`;
<<HOL message: inventing new type variable names: 'a, 'b, 'c.>>
> val it = `p /\ q` : term
- strip_comb it;
> val it = (`$/\`, [`p`, `q`]) : term * term list
- dest_var (#1 it);
> val it = ("/\\", `:'a -> 'b -> 'c`) : string * hol_type
```

When writing library code that calls the parser, it can be useful to
know exactly what constants the parser will "recognise".

### Comments

This function does not affect the contents of a theory. A constant made
invisible using this call is still really present in the theory; it is
just harder to find.

### See also

[`Parse.hidden`](#Parse.hidden), [`Parse.hide`](#Parse.hide),
[`Parse.known_constants`](#Parse.known_constants),
[`Parse.reveal`](#Parse.reveal)
