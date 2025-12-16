## `print_theory_as_tex`

``` hol4
EmitTeX.print_theory_as_tex : string -> unit
```

------------------------------------------------------------------------

Emits a theory as LaTeX commands.

An invocation of `print_theory_as_tex thy` will export the named theory
as a collection of LaTeX commands. The output file is named
"HOLthy.tex", where `thy` is the named theory. The prefix "HOL" can be
changed by setting `holPrefix`. The file is stored in the directory
`emitTeXDir`. By default the current working directory is used.

The LaTeX file will contain commands for displaying the theory's
datatypes, definitions and theorems.

### Failure

Will fail if there is a system error when trying to write the file. If
the theory is not loaded then a message will be printed and an empty
file will be created.

### Example

The list theory is exported with:

``` hol4
 - EmitTeX.print_theory_as_tex "list";
 > val it = () : unit
```

The resulting file can be included in a LaTeX document with

``` hol4
 \input{HOLlist}
```

Some examples of the available LaTeX commands are listed below:

``` hol4
 \HOLlistDatatypeslist
 \HOLlistDefinitionsALLXXDISTINCT
 \HOLlistTheoremsALLXXDISTINCTXXFILTER
```

Underscores in HOL names are replaced by "XX"; quotes become "YY" and
numerals are expanded out e.g. "1" becomes "One".

Complete listings of the datatypes, definitions and theorems are
displayed with:

``` hol4
 \HOLlistDatatypes
 \HOLlistDefinitions
 \HOLlistTheorems
```

The date the theory was build can be displayed with:

``` hol4
 \HOLlistDate
```

The generated LaTeX will reflect the output of `Parse.thm_to_string`,
which is under the control of the user. For example, the line width can
be changed by setting `Globals.linewidth`.

The Verbatim display environment is used, however, "boxed" versions can
be constructed. For example,

``` hol4
 \BUseVerbatim{HOLlistDatatypeslist}
```

can be used inside tables and figures.

### Comments

The LaTeX style file `holtexbasic.sty` (or `holtex.sty`) should be used.
These style files can be modified by the user. For example, the font can
be changed to Helvetica with

``` hol4
 \fvset{fontfamily=helvetica}
```

However, note that this will adversely effect the alignment of the
output.

### See also

[`EmitTeX.print_term_as_tex`](#EmitTeX.print_term_as_tex),
[`EmitTeX.print_type_as_tex`](#EmitTeX.print_type_as_tex),
[`EmitTeX.print_theorem_as_tex`](#EmitTeX.print_theorem_as_tex),
[`EmitTeX.print_theories_as_tex_doc`](#EmitTeX.print_theories_as_tex_doc),
[`EmitTeX.tex_theory`](#EmitTeX.tex_theory)
