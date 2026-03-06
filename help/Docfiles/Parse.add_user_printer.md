## `add_user_printer`

``` hol4
Parse.add_user_printer : (string * term) -> unit
```

------------------------------------------------------------------------

Adds a user specified pretty-printer for a specified type.

The function `add_user_printer` is used to add a special purpose term
pretty-printer to the interactive system. The pretty-printer is called
whenever the term to be printed matches (with `match_term`) the term
provided as the second parameter. If multiple calls to
`add_user_printer` are made with the same string parameter, the older
functions are replaced entirely. If multiple printers match, the more
specific match will be chosen. If two matches are equally specific, the
match chosen is unspecified.

The function that performs the printing is not given directly, but is
instead referred to by name (the first parameter to `add_user_printer`).
This name must be linked to the desired code with a call to
`term_grammar.userSyntaxFns.register_userPP`, which function should be
called within another ML file (i.e., not the "Script'' file of the
theory). The name passed to the `register_userPP` function is then the
name that must also be passed to `add_user_printer`. The term argument
is the desired pattern.

Alternatively, if the name specified is the empty string (`""`), the
behaviour is to ensure that terms matching this pattern are not handled
by the user-printing machinery. The expectation is that a more general
pattern has already been registered, but that in this specified scenario
the general term-printing machinery should be used.

The user-supplied function may choose not to print anything for the
given term and hand back control to the standard printer by raising the
exception `term_pp_types.UserPP_Failed`. All other exceptions will
propagate to the top-level. If the system printer receives the
`UserPP_Failed` exception, it prints out the term using its standard
algorithm, but will again attempt to call the user function on any
sub-terms that match the pattern.

The type `userprinter` is an abbreviation defined in `term_grammar` to
be

``` hol4
   type userprinter =
     type_grammar.grammar * term_grammar.grammar ->
     PPBackend.t ->
     sysprinter ->
     term_pp_types.ppstream_funs ->
     (grav * grav * grav) -> int ->
     term -> uprinter
```

where the type `grav` (from `term_pp_types`) is

``` hol4
   datatype grav = Top | RealTop | Prec of (int * string)
```

The type `uprinter` (standing for "unit printer'') is a special monadic
printing type based on the `smpp` module (explained further in the
example below). The type `sysprinter` is another abbreviation

``` hol4
   type sysprinter =
     { gravs : (grav * grav * grav), binderp : bool,
       depth : int } -> term -> uprinter
```

Thus, when the user's printing function is called, it is passed ten
parameters, including three "gravity'' values in a triple, and two
grammars. The fourth parameter is the system's own printer. The fifth
parameter is a record of functions to call for adding a string to the
output, adding a break, adding new lines, defining some styles for
printing like the color, etc. The availability of the system's printer
allows the user function to use the default printer on sub-terms that it
is not interested in. The user function must not call the `sysprinter`
on the term that it is handed initially as the `sysprinter` will
immediately call the user printing function all over again. If the user
printer wants to give the whole term back to the system printer, then it
must use the `UserPP_Failed` exception described above.

Though there are existing functions `add_string`, `add_break` etc. that
can be used to create pretty-printing values, users should prefer
instead to use the functions that are provided in the triple with the
`sysprinter`. This then gives them access to functions that can prevent
inadvertent symbol merges.

The `grav` type is used to let pretty-printers know a little about the
context in which a term is to be printed out. The triple of gravities is
given in the order "parent", "left" and "right". The left and right
gravities specify the precedence of any operator that might be
attempting to "grab" arguments from the left and right. For example, the
term

``` hol4
   (p /\ (if q then r else s)) ==> t
```

should be pretty-printed as

``` hol4
   p /\ (if q then r else s) ==> t
```

The system figures this out when it comes to print the conditional
expression because it knows both that the operator to the left has the
appropriate precedence for conjunction but also that there is an
operator with implication's precedence to the right. The issue arises
because conjunction is tighter than implication in precedence, leading
the printer to decide that parentheses aren't necessary around the
conjunction. Similarly, considered on its own, the conjunction doesn't
require parentheses around the conditional expression because there is
no competition between them for arguments.

The `grav` constructors `Top` and `RealTop` indicate a context analogous
to the top of the term, where there is no binding competition. The
constructor `RealTop` is reserved for situations where the term really
is the top of the tree; `Top` is used for analogous situations such when
the term is enclosed in parentheses. (In the conditional expression
above, the printing of `q` will have `Top` gravities to the left and
right.)

The `Prec` constructor for gravity values takes both a number indicating
precedence level and a string corresponding to the token that has this
precedence level. This string parameter is of most importance in the
parent gravity (the first component of the triple) where it can be
useful in deciding whether or not to print parentheses and whether or
not to begin fresh pretty-printing blocks. For example, tuples in the
logic look better if they have parentheses around the topmost instance
of the comma-operator, regardless of whether or not this is required
according to precedence considerations. By examining the parent gravity,
a printer can determine more about the term's context. (Note that the
parent gravity will also be one or other of the left and right
gravities; but it is not possible to tell which.)

The integer parameter to both the system printing function and the user
printing function is the depth of the term. The system printer will stop
printing a term if the depth ever reaches exactly zero. Each time it
calls itself recursively, the depth parameter is reduced by one. It
starts out at the value stored in `Globals.max_print_depth`. Setting the
latter to `~1` will ensure that all of a term is always printed.

The `binderp` parameter to the system-printer is true when the term to
be printed should be considered as a binder. This makes a difference
when the printer comes to print type annotations: annotations will occur
with variables if the variable is in a binding position, and not
elsewhere. This logic ensures that a term like `\x. x` prints as
`\x:'a. x`. The first, binding occurrence of the variable gets an
annotation; subsequent occurrences do not.

### Failure

Fails if the string parameter does not correspond to a name used to
register a function with `term_grammar.userSyntaxFns.register_userPP`.
In addition, if the function parameter fails to print all terms of the
registered type in any other way than raising the `UserPP_Failed`
exception, then the pretty-printer will also fail.

### Example

In the examples that follow, the companion `temp_add_userprinter`
function is used: this function takes a value of type `userprinter`
directly, and so is a more direct demonstration of how user-printers can
behave. The boilerplate required for preserved-across-`export_theory`
functionality starts with the external module. For a theory
`fooScript.sml`, one might write the file `fooPP.sml`:

``` hol4
   structure fooPP =
   struct

     fun term_printer_code ... = ...
     val _ = term_grammar.userSyntaxFns.register_userPP {
               name = "foo.term_printer", code = term_printer_code
             }
   end
```

where `term_printer_code` has type `userprinter`. Note that the code for
the printer has to be written so that it can be compiled before the
theory `foo` is in context. In particular, top-level calls to
`mk_thy_const` and the like will fail if they attempt to bind constants
declared in theory `foo`.

In `fooScript.sml`, the following is the idiom required:

``` hol4
   local open fooPP in end;
   val _ = add_ML_dependency "fooPP"
   val _ = add_user_printer ("foo.term_printer", ``term pattern``)
```

As discussed, the remaining examples use `temp_add_user_printer`. The
first example uses the system printer to print sub-terms, and concerns
itself only with printing conjunctions. Note how the actions that make
up the pretty-printer (combinations of `add_string` and `add_break` are
combined with the infix `>>` operator (from the `smpp` module).

``` hol4
  > fun myprint Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
    let
      open Portable term_pp_types smpp
      val (str,brk) = (#add_string ppfns, #add_break ppfns);
      val (l,r) = dest_conj t
      fun syspr gravs =
        sys {gravs = gravs, depth = d - 1, binderp = false}
    in
      str "CONJ:" >>
      brk (1,0) >>
      syspr (Top, Top, Top) l >>
      brk (1,0) >> str "and then" >> brk(1,0) >>
      sys (Top, Top, Top) r >>
      str "ENDCONJ"
    end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;
  val myprint = fn :
     'a -> 'b ->
     (grav * grav * grav -> int -> term ->
       (term_pp_types.printing_info,'c)smpp.t) ->
     term_pp_types.ppstream_funs -> 'd -> int -> term ->
     (term_pp_types.printing_info,unit)smpp.t

  > temp_add_user_printer ("myprint", ``p /\ q``, myprint);
  val it = () : unit

  > ``p ==> q /\ r``;
  val it = ``p ==> CONJ: q and then r ENDCONJ`` : term
```

The variables `p`, `q` and `r` as well as the implication are all of
boolean type, but are handled by the system printer. The user printer
handles just the special form of the conjunction. Note that this example
actually falls within the scope of the `add_rule` functionality.

The next approach to printing conjunctions is not possible with
`add_rule`. This example uses the styling and blocking functions to
create part of its effect. These functions (`ustyle` and `ublock`
respectively) are higher-order functions that take printers as arguments
and cause the arguments to be printed with a particular governing style
(`ustyle`), or indented to reveal block structure (`ublock`).

``` hol4
  - fun myprint2 Gs B sys (ppfns:term_pp_types.ppstream_funs) (pg,lg,rg) d t =
    let
      open Portable term_pp_types PPBackEnd smpp
      val {add_string,add_break,ublock,ustyle,...} = ppfns
      val (l,r) = dest_conj t
      fun delim wrap body =
        case pg of
          Prec(_, "CONJ") => body
        | _ => wrap body
      fun syspr t =
        sys {gravs = (Prec(0,"CONJ"), Top, Top), depth = d - 1,
             binderp = false} t
    in
      delim (fn bod => ublock CONSISTENT 0
                         (ustyle [Bold] (add_string "CONJ") >>
                          add_break (1,2) >>
                          ublock INCONSISTENT 0 bod >>
                          add_break (1,0) >>
                          ustyle [Bold] (add_string "ENDCONJ")))
         (syspr l >> add_string "," >> add_break (1,0) >> syspr r)
    end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

  - temp_add_user_printer ("myprint2", ``p /\ q``, myprint2);

  - ``p /\ q /\ r /\ s /\ t /\ u /\ p /\ p /\ p /\ p /\ p /\ p /\
      p /\ p /\ p /\ p/\ p /\ p /\ q /\ r /\ s /\ t /\ u /\ v /\
      (w /\ x) /\ (p \/ q) /\ r``;

  > val it =
      ``CONJ
          p, q, r, s, t, u, p, p, p, p, p, p, p, p, p, p, p, p, q,
          r, s, t, u, v, w, x, p \/ q, r
        ENDCONJ`` : term
```

This example also demonstrates using parent gravities to print out a big
term. The function passed as an argument to delim is only called when
the parent gravity is not `"CONJ"`. This ensures that the special
delimiters only get printed when the first conjunction is encountered.
Subsequent, internal conjunctions get passed the `"CONJ"` gravity in the
calls to `sys`.

A better approach (and certainly a more direct one) would probably be to
call `strip_conj` and print all of the conjuncts in one fell swoop.
Additionally, this example demonstrates how easy it is to conceal
genuine syntactic structure with a pretty-printer. Finally, it shows how
styles can be used.

For extending the pretty-printer in ways not possible to encompass with
the built-in grammar rules for concrete syntax.

### See also

[`Parse.add_rule`](#Parse.add_rule),
[`Term.match_term`](#Term.match_term),
[`Parse.remove_user_printer`](#Parse.remove_user_printer)
