open Holparse
open Holparsesupp
open Holparsetools
open Simpledump

let texdoc = parse_chan ModeTex tex_main stdin

let s = dumptexdoc texdoc

let _ = print_string s
