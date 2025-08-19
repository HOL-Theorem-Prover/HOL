## `add_listform`

``` hol4
Parse.add_listform :
  {separator : pp_element list, leftdelim : pp_element list,
   rightdelim : pp_element list, cons : string, nilstr : string,
   block_info : term_grammar.block_info } ->
  unit
```

------------------------------------------------------------------------

Adds a "list-form" to the built-in grammar, allowing the parsing of
strings such as `[a; b; c]` and `{}`.

The `add_listform` function allows the user to augment the HOL parser
with rules so that it can turn a string of the form

``` hol4
   <ld> str1 <sep> str2 <sep> ... strn <rd>
```

into the term

``` hol4
   <cons> t1 (<cons> t2 ... (<cons> tn <nilstr>))
```

where `<ld>` is the left delimiter string, `<rd>` the right delimiter,
and `<sep>` is the separator string from the fields of the record
argument to the function. The various `stri` are strings representing
the `ti` terms. Further, the grammar will also parse `<ld> <rd>` into
`<nilstr>`.

The `pp_element` lists passed to this function for the `separator`,
`leftdelim` and `rightdelim` fields are interpreted as by the `add_rule`
function. These lists must have exactly one `TOK` element (this provides
the string that will be printed), and other formatting elements such as
`BreakSpace`.

The `block_info` field is a pair consisting of a "consistency"
(`PP.CONSISTENT`, or `PP.INCONSISTENT`), and an indentation depth (an
integer). The standard value for this field is `(PP.INCONSISTENT,0)`,
which will cause lists too long to fit in a single line to print with as
many elements on the first line as will fit, and for subsequent elements
to appear unindented on subsequent lines. Changing the "consistency" to
`PP.CONSISTENT` would cause lists too long for a single line to print
with one element per line. The indentation level number specifies the
number of extra spaces to be inserted when a line-break occurs.

In common with the `add_rule` function, there is no requirement that the
`cons` and `nilstr` fields be the names of constants; the parser/grammar
combination will generate variables with these names if there are no
corresponding constants.

The HOL pretty-printer is simultaneously aware of the new rule, and
terms of the forms above will print appropriately.

### Failure

Fails if any of the `pp_element` lists are ill-formed: if they include
`TM`, `BeginFinalBlock`, or `EndInitialBlock` elements, or if do not
include exactly one `TOK` element. Subsequent calls to the term parser
may also fail or behave unpredictably if the strings chosen for the
various fields above introduce precedence conflicts. For example, it
will almost always be impossible to use left and right delimiters that
are already present in the grammar, unless they are there as the left
and right parts of a closefix.

### Example

The definition of the "list-form" for lists in the HOL distribution is:

``` hol4
   add_listform {separator = [TOK ";", BreakSpace(1,0)],
                 leftdelim = [TOK "["], rightdelim = [TOK "]"],
                 cons = "CONS", nilstr = "NIL",
                 block_info = (PP.INCONSISTENT, 0)};
```

while the set syntax is defined similarly:

``` hol4
   add_listform {leftdelim = [TOK "{"], rightdelim = TOK ["}"],
                 separator = [";", BreakSpace(1,0)],
                 cons = "INSERT", nilstr = "EMPTY",
                 block_info = (PP.INCONSISTENT, 0)};
```

Used to make sequential term structures print and parse more pleasingly.

### Comments

As with other parsing functions, there is a `temp_add_listform` version
of this function, which has the same effect on the global grammar, but
which does not cause this effect to persist when the current theory is
exported.

### See also

[`Parse.add_rule`](#Parse.add_rule)
