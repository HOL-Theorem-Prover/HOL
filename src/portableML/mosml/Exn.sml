structure Exn :> Exn =
struct

  datatype 'a result = Res of 'a | Exn of exn

  fun get_res (Res x) = SOME x
    | get_res (Exn _) = NONE

  fun get_exn (Res _) = NONE
    | get_exn (Exn e) = SOME e

  fun capture f x = Res (f x) handle e => Exn e

  fun release (Res x) = x
    | release (Exn e) = raise e

end
