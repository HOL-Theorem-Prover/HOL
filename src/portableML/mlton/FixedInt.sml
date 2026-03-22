structure FixedInt = struct
  type int = Int.int
  val fromInt = fn (n : Int.int) => n
  val toString = Int.toString
end
