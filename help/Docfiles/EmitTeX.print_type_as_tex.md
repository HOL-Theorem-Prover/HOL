## `print_type_as_tex`

``` hol4
EmitTeX.print_type_as_tex : hol_type -> unit
```

------------------------------------------------------------------------

Prints a type as LaTeX.

An invocation of `print_type_as_tex ty` will print the type `ty`,
replacing various character patterns (e.g. `#` and `->`) with LaTeX
commands. The translation is controlled by the string to string function
`EmitTeX.hol_to_tex`.

### Failure

Should never fail.

### Example

``` hol4
 - EmitTeX.print_type_as_tex ``:bool # bool -> num`` before print "\n";
 :bool \HOLTokenProd{} bool \HOLTokenMap{} num
 > val it = () : unit
```

### Comments

The LaTeX style file `holtexbasic.sty` (or `holtex.sty`) should be used
and the output should be pasted into a Verbatim environment.

### See also

[`EmitTeX.print_term_as_tex`](#EmitTeX.print_term_as_tex),
[`EmitTeX.print_theorem_as_tex`](#EmitTeX.print_theorem_as_tex),
[`EmitTeX.print_theory_as_tex`](#EmitTeX.print_theory_as_tex),
[`EmitTeX.print_theories_as_tex_doc`](#EmitTeX.print_theories_as_tex_doc),
[`EmitTeX.tex_theory`](#EmitTeX.tex_theory)
