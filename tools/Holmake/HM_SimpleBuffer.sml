structure HM_SimpleBuffer :> HM_SimpleBuffer =
struct

fun mkBuffer () = let
  val buf = ref ([] : string list)
  fun push s = buf := s :: !buf
  fun read () = let
    val contents = String.concat (List.rev (!buf))
  in
    buf := [contents];
    contents
  end
  fun reset() = buf := []
in
  {push = push, read = read, reset = reset}
end

end (* struct *)
