## `print_theorem_as_tex`

``` hol4
EmitTeX.print_theorem_as_tex : thm -> unit
```

------------------------------------------------------------------------

Prints a theorem as LaTeX.

An invocation of `print_theorem_as_tex thm` will print the term `thm`,
replacing various character patterns (e.g. `/\` and `\/`) with LaTeX
commands. The translation is controlled by the string to string function
`EmitTeX.hol_to_tex`. If the theorem is for a datatype then the function
`datatype_thm_to_string` is used to produce the orginal declaration.

### Failure

Should never fail.

### Example

``` hol4
 - EmitTeX.print_theorem_as_tex listTheory.CONS before print "\n";
 \HOLTokenTurnstile{} \HOLTokenForall{}l. \HOLTokenNeg{}NULL l \HOLTokenImp{} (HD l::TL l = l)
 > val it = () : unit
 - EmitTeX.print_theorem_as_tex listTheory.datatype_list before print "\n";
 list = [] | CONS of \HOLTokenQuote{}a \HOLTokenImp{} \HOLTokenQuote{}a list
 > val it = () : unit
```

### Comments

The LaTeX style file `holtexbasic.sty` (or `holtex.sty`) should be used
and the output should be pasted into a Verbatim environment.

### See also

[`EmitTeX.print_term_as_tex`](#EmitTeX.print_term_as_tex),
[`EmitTeX.print_type_as_tex`](#EmitTeX.print_type_as_tex),
[`EmitTeX.print_theory_as_tex`](#EmitTeX.print_theory_as_tex),
[`EmitTeX.print_theories_as_tex_doc`](#EmitTeX.print_theories_as_tex_doc),
[`EmitTeX.tex_theory`](#EmitTeX.tex_theory)
