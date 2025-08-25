structure ThreadLocal :> ThreadLocal =
struct

  type 'a t = 'a option ref
  fun new () = ref NONE
  fun get r = !r
  fun set (r, v) = r := SOME v

end
