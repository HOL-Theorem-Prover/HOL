## `print_theories_as_tex_doc`

``` hol4
EmitTeX.print_theories_as_tex_doc : string list -> string -> unit
```

------------------------------------------------------------------------

Emits theories as LaTeX commands and creates a document template.

An invocation of `print_theories_as_tex_doc thys name` will export the
named theories `thys` as a collection of LaTeX commands and it will also
generate a document, whose file name is given by `name`, that presents
all of the theories. The theories are exported with
`print_theory_as_tex`.

### Failure

Will fail if there is a system error when trying to write the files. It
will not overwite the file `name`, however, the theories may be
overwritten.

### Example

The invocation

``` hol4
 - EmitTeX.print_theories_as_tex_doc ["arithmetic", "list", "words"] "report";
 > val it = () : unit
```

will generate four files "HOLarithmetic.tex", "HOLlist.tex",
"HOLwords.tex" and "report.tex".

The document can be built as follows:

``` hol4
 $ cp $HOLHOME/src/emit/holtex.sty .
 $ pdflatex report
 $ makeindex report
 $ pdflatex report
```

### See also

[`EmitTeX.print_term_as_tex`](#EmitTeX.print_term_as_tex),
[`EmitTeX.print_type_as_tex`](#EmitTeX.print_type_as_tex),
[`EmitTeX.print_theorem_as_tex`](#EmitTeX.print_theorem_as_tex),
[`EmitTeX.print_theory_as_tex`](#EmitTeX.print_theory_as_tex),
[`EmitTeX.tex_theory`](#EmitTeX.tex_theory)
