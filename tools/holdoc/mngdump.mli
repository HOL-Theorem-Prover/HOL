exception BadArg of string Holdocmodel.located
val format_badarg : string Holdocmodel.located -> string
val write_warning : string Holdocmodel.located -> unit
val wrap : string -> string -> ('a -> unit) -> 'a -> unit
val replicate : int -> 'a -> 'a list
val texify_math : string -> string
val texify_text : string -> string
type pvars = string list
val potential_vars : Holdocmodel.holdoc -> pvars
val munge_ident : pvars -> string -> unit
val munge_symbol : pvars -> bool -> string -> unit
val munge_texify_text : string -> unit
val munge_texify_math : string -> unit
val munge_indent : int -> unit
val munge_hol_content : pvars -> Holdocmodel.hol_content -> unit
val render_HolTex_hook : (pvars -> Holdocmodel.texdoc -> unit) ref
val munge_curried :
  pvars ->
  Holdocmodel.hol_content ->
  Holdoc_init.curried_info -> Holdocmodel.holdoc -> Holdocmodel.holdoc
val munge_holdoc : pvars -> Holdocmodel.holdoc -> unit
val rendertexdoc : Holdocmodel.texdoc -> unit
val rendertexdoc_pvs : pvars -> Holdocmodel.texdoc -> unit
val rendertexdoc_content : Holdocmodel.texdoc_content -> unit
val rendertexdoc_content_pvs : pvars -> Holdocmodel.texdoc_content -> unit
val texrenderdirective : Holdocmodel.directive -> unit
val texrenderdirective_content : Holdocmodel.directive -> unit
val renderholdoc : Holdocmodel.holdoc -> unit
val renderholdoc_pvs : pvars -> Holdocmodel.holdoc -> unit
val dump_unseen_strings : unit -> unit

