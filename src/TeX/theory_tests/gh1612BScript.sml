Theory gh1612B
Ancestors gh1612A
Libs EmitTeX

val _ = OS.FileSys.remove "evenReport.tex" handle _ => ()

val _ = print_theories_as_tex_doc ["gh1612A"] "evenReport"
