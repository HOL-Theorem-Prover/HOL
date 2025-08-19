## `show_types`

``` hol4
Globals.show_types : bool ref
```

------------------------------------------------------------------------

Flag controlling printing of HOL types (in terms).

Normally HOL types in terms are not printed, since this makes terms hard
to read. Type printing is enabled by `show_types := true`, and disabled
by `show_types := false`. When printing of types is enabled, not all
variables and constants are annotated with a type. The intention is to
provide sufficient type information to remove any ambiguities without
swamping the term with type information.

### Failure

Never fails.

### Example

``` hol4
- BOOL_CASES_AX;;
> val it = |- !t. (t = T) \/ (t = F) : thm

- show_types := true;
> val it = () : unit

- BOOL_CASES_AX;;
> val it = |- !(t :bool). (t = T) \/ (t = F) : thm
```

### Comments

It is possible to construct an abstraction in which the bound variable
has the same name but a different type to a variable in the body. In
such a case the two variables are considered to be distinct. Without
type information such a term can be very misleading, so it might be a
good idea to provide type information for the free variable whether or
not printing of types is enabled.

### See also

[`Parse.print_term`](#Parse.print_term)
