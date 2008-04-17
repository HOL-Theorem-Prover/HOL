open Holparse
open Holparsesupp
open Holparsetools
open Simpledump

let mosmldoc = parse_chan ModeMosml mosml_main stdin

let s = dumpmosmldoc mosmldoc

let _ = print_string s
