(* simpletexdump.ml -- test for Hollex *)
(* Keith Wansbrough 2001 *)

open Hollex

let go t = print_string ((render_token t)^" ")

let _ = Stream.iter go (textokstream stdin)

