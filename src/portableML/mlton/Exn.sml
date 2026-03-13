structure Exn =
struct
  datatype 'a result = Res of 'a | Exn of exn
  fun capture f x = Res (f x) handle e => Exn e
  fun release (Res x) = x
    | release (Exn e) = raise e
end
