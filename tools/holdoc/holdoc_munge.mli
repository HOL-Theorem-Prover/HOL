(* holdoc_munge.ml -- process HOL LTS or TeX or HOL into LaTeX code (library) *)
(* Keith Wansbrough 2001 *)


(* render stdin (a HOL spec of the LTS) into LaTeX on stdout *)
val lts_latex_render : unit -> unit

(* render stdin (LaTeX with embedded HOL) into LaTeX on stdout *)
val mng_latex_render : unit -> unit

