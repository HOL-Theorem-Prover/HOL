## `print_term_as_tex`

``` hol4
EmitTeX.print_term_as_tex : term -> unit
```

------------------------------------------------------------------------

Prints a term as LaTeX.

An invocation of `print_term_as_tex tm` will print the term `tm`,
replacing various character patterns (e.g. `/\` and `\/`) with LaTeX
commands. The translation is controlled by the string to string function
`EmitTeX.hol_to_tex`.

### Failure

Should never fail.

### Example

``` hol4
 - EmitTeX.print_term_as_tex ``\l h. {x | l <= x /\ x <= h}`` before print "\n";
 \HOLTokenLambda{}l h. \HOLTokenLeftbrace{}x | l \HOLTokenLeq{} x \HOLTokenConj{} x \HOLTokenLeq{} h\HOLTokenRightbrace{}
 > val it = () : unit
```

### Comments

The LaTeX style file `holtexbasic.sty` (or `holtex.sty`) should be used
and the output should be pasted into a Verbatim environment.

### See also

[`EmitTeX.print_type_as_tex`](#EmitTeX.print_type_as_tex),
[`EmitTeX.print_theorem_as_tex`](#EmitTeX.print_theorem_as_tex),
[`EmitTeX.print_theory_as_tex`](#EmitTeX.print_theory_as_tex),
[`EmitTeX.print_theories_as_tex_doc`](#EmitTeX.print_theories_as_tex_doc),
[`EmitTeX.tex_theory`](#EmitTeX.tex_theory)
