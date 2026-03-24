structure Unsynchronized =
struct
  fun inc i = (i := !i + 1; !i)
end
