(* lts_to_latex.ml -- turn LTS (in HOL) into LaTeX code *)
(* Keith Wansbrough 2001 *)


open Holdoc_init
open Holdoc_munge

let _ = !curmodals.rULES := true

let _ =
  lts_latex_render ()

