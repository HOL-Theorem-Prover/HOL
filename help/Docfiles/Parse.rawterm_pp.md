## `rawterm_pp`

``` hol4
Parse.rawterm_pp : ('a -> 'b) -> 'a -> 'b
```

------------------------------------------------------------------------

Causes a function to use the raw terminal backend when pretty-printing.

Functions that pretty-print HOL types, terms and theorems do so through
an abstraction called a "backend". Using these backends allows output to
be customised to the facilities provided by different display devices.
For example, on terminals supporting DEC's vt100 colour coding, free
variables are displayed in blue. There is also a "raw terminal" backend,
that doesn't change the output in any way.

When an interactive session begins, HOL links all of the pretty-printing
functions to a backend value stored in a reference,
`Parse.current_backend`. Of course, this reference can be changed as a
user desires. A call to `rawterm_pp f` function wraps a call to
`Lib.with_flag`, setting the current backend to be the raw terminal
value for the duration of the `f`'s application to its (first) argument.

### Failure

A call to `rawterm_pp f` never fails. A call to `rawterm_pp f x` should
only fail if `f x` would fail, but this ultimately depends on `f`'s
implementation.

### Example

In a `vt100`-compatible terminal, capturing the output of `pp_term`
reveals a stream of horrible-looking escape codes:

``` hol4
   > ppstring pp_term ``p /\ q``;
   val it = "\^[[0;1;34mp\^[[0m /\\ \^[[0;1;34mq\^[[0m": string
```

If this string is to be `print`-ed to the `vt100`, it will colour the
`p` and `q` a pleasant blue colour. If, on the other hand, the string is
to be output to a file, the colouring is probably not desirable. Then
one can use `rawterm_pp` to get the unadorned characters of the output:

``` hol4
   > rawterm_pp (ppstring pp_term) ``p /\ q``;
   val it = "p /\\ q": string
```

This last usage is so common that it is already available in the library
as `term_to_string`.

### Comments

If a function `f` is curried with multiple arguments, say `f x y`, then
care will probably be needed with modifying it with `rawterm_pp`. In
particular, `rawterm_pp f x y` is likely not to work, while
`rawterm_pp (f x) y` probably will.

### See also

[`Lib.ppstring`](#Lib.ppstring),
[`Parse.term_to_string`](#Parse.term_to_string),
[`Lib.with_flag`](#Lib.with_flag)
