## `uptodate_type`

``` hol4
Theory.uptodate_type : hol_type -> bool
```

------------------------------------------------------------------------

Tells if a type is out of date.

Operations in the current theory segment of HOL allow one to redefine
types and constants. This can cause theorems to become invalid. As a
result, HOL has a rudimentary consistency maintenance system built
around the notion of whether type operators and term constants are
"up-to-date".

An invocation `uptodate_type ty`, checks `ty` to see if it has been
built from any out of date components, returning `false` just in case it
has. The definition of `out-of-date` is mutually recursive among types,
terms, and theorems. A type variable never out-of-date. A compound type
is out-of-date if either (a) its type operator is out-of-date, or (b)
any of its argument types are out-of-date. A type operator is
out-of-date if it has been re-declared or if the witness theorem used to
justify the type in the call to `new_type_definition` is out-of-date.
Only a component of the current theory segment may be out-of-date. All
items from ancestor theories are fixed, and unable to be overwritten,
thus are always up-to-date.

### Failure

Never fails.

### Example

``` hol4
- Hol_datatype `foo = A | B of 'a`;
<<HOL message: Defined type: "foo">>
> val it = () : unit

- val ty = Type `:'a foo list`;
> val ty = `:'a foo list` : hol_type

- uptodate_type ty;
> val it = true : bool

- delete_type "foo";
> val it = () : unit

- uptodate_type ty;
> val it = false : bool
```

### See also

[`Theory.uptodate_term`](#Theory.uptodate_term),
[`Theory.uptodate_thm`](#Theory.uptodate_thm)
