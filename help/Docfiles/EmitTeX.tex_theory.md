## `tex_theory`

``` hol4
EmitTeX.tex_theory : string -> unit
```

------------------------------------------------------------------------

Emits theory as LaTeX commands and creates a document template.

An invocation of `tex_theory thy` will export the named theory `thy` as
a collection of LaTeX commands and it will also generate a document
"thy.tex" that presents the theory. The string `"-"` may be used to
denote the current theory segment. The theory is exported with
`print_theory_as_tex`.

### Failure

Will fail if there is a system error when trying to write the files. It
will not overwite the file `name`, however, "HOLname.tex" may be
overwritten.

### Example

The invocation

``` hol4
 - EmitTeX.tex_theory "list";
 > val it = () : unit
```

will generate two files "HOLlist.tex" and "list.tex".

### See also

[`EmitTeX.print_term_as_tex`](#EmitTeX.print_term_as_tex),
[`EmitTeX.print_type_as_tex`](#EmitTeX.print_type_as_tex),
[`EmitTeX.print_theorem_as_tex`](#EmitTeX.print_theorem_as_tex),
[`EmitTeX.print_theory_as_tex`](#EmitTeX.print_theory_as_tex),
[`EmitTeX.print_theories_as_tex_doc`](#EmitTeX.print_theories_as_tex_doc)
